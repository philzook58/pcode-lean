#include <ghidra/context.hh>
#include <ghidra/loadimage.hh>
#include <ghidra/marshal.hh>
#include <ghidra/pcoderaw.hh>
#include <ghidra/sleigh.hh>
#include <ghidra/xml.hh>
#include <algorithm>
#include <cctype>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace ghidra;
namespace {
struct Node { std::string space; uint64_t offset; unsigned size; };
struct Op { OpCode code; std::optional<Node> out; std::vector<Node> in; std::string space; };
struct Insn { uint64_t address; unsigned length; std::string text; std::vector<Op> ops; };
struct Reg { std::string name; uint64_t offset; unsigned size; };
using Temps = std::map<std::pair<uint64_t, unsigned>, std::string>;

/** Everything architecture-specific: specs, register cells, and the generated state type. */
struct Arch {
  std::string name, type, sla, pspec, state, pc;
  unsigned addrBytes;
  std::vector<std::string> regs;
  std::vector<std::string> calls;    // mnemonics rejected: this version stops at the first RETURN
};
const std::vector<Arch> ARCHS = {
  {"x86-64", "x86:LE:64:default", PCODE_SPEC_DIR "/x86-64.sla", PCODE_SPEC_DIR "/x86-64.pspec", "X86State",
   "rip", 8, {"RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI", "R8", "R9", "R10", "R11", "R12", "R13",
              "R14", "R15", "RIP", "CF", "PF", "AF", "ZF", "SF", "DF", "OF"}, {"CALL", "CALLF"}},
  {"riscv32", "RISCV:LE:32:default", PCODE_RISCV_DIR "/riscv.ilp32d.sla", PCODE_RISCV_DIR "/RV32.pspec",
   "RV32State", "pc", 4, {"zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2",
              "a3", "a4", "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
              "t3", "t4", "t5", "t6", "pc"}, {"jal", "jalr", "c.jal", "c.jalr"}},
};

std::string number(uint64_t n) { std::ostringstream s; s << "0x" << std::hex << n; return s.str(); }
std::string literal(uint64_t n, unsigned bits) {
  return "(" + number(n) + " : BitVec " + std::to_string(bits) + ")";
}
Node node(const VarnodeData &n) {
  if (n.size <= 0 || n.size > 8) throw std::runtime_error("only 1..8-byte varnodes are supported");
  return {n.space->getName(), n.offset, static_cast<unsigned>(n.size)};
}
class Image : public LoadImage {
public:
  uint64_t base;
  std::vector<unsigned char> bytes;
  std::string type;
  Image(uint64_t base, std::vector<unsigned char> bytes, std::string type)
    : LoadImage("raw"), base(base), bytes(std::move(bytes)), type(std::move(type)) {}
  void loadFill(unsigned char *out, int size, const Address &address) override {
    auto start = address.getOffset();
    for (int i = 0; i < size; ++i) {
      uint64_t p = start + i;
      out[i] = p >= base && p - base < bytes.size() ? bytes[p - base] : 0;
    }
  }
  std::string getArchType() const override { return type; }
  void adjustVma(long) override { throw std::runtime_error("image relocation is unsupported"); }
};
class Capture : public PcodeEmit {
public:
  std::vector<Op> ops;
  void dump(const Address &, OpCode code, VarnodeData *out, VarnodeData *in, int count) override {
    Op op{code, {}, {}, ""};
    if (out) op.out = node(*out);
    for (int i = 0; i < count; ++i) op.in.push_back(node(in[i]));
    if (code == CPUI_LOAD || code == CPUI_STORE) op.space = in[0].getSpaceFromConst()->getName();
    ops.push_back(std::move(op));
  }
};
class Assembly : public AssemblyEmit {
public:
  std::string text, mnemonic;
  void dump(const Address &, const std::string &name, const std::string &body) override {
    mnemonic = name;
    text = name + (body.empty() ? "" : " " + body);
  }
};

class Printer {
  const std::vector<Insn> &code;
  const std::vector<Reg> &regs;
  const Arch &arch;
  std::map<uint64_t, size_t> labels;
  std::ostream &out;
  unsigned serial = 0, emitted = 0;
  const Reg &reg(const Node &n) const {
    for (const auto &r : regs)
      if (n.offset >= r.offset && n.offset - r.offset + n.size <= r.size) return r;
    throw std::runtime_error("unsupported register at " + number(n.offset));
  }
  std::string slice(const std::string &value, unsigned offset, unsigned size, unsigned total) const {
    if (offset == 0 && size == total) return value;
    return "(BitVec.extractLsb' " + std::to_string(offset * 8) + " " +
      std::to_string(size * 8) + " " + value + ")";
  }
  std::string read(const Node &n, const Temps &temps) const {
    if (n.space == "const") return literal(n.offset, n.size * 8);
    if (n.space == "register") {
      const auto &r = reg(n);
      return slice("s." + r.name, n.offset - r.offset, n.size, r.size);
    }
    if (n.space == "unique") {
      for (const auto &[key, value] : temps)
        if (n.offset >= key.first && n.offset - key.first + n.size <= key.second)
          return slice(value, n.offset - key.first, n.size, key.second);
      throw std::runtime_error("read of uninitialized/partially overwritten temporary " + number(n.offset));
    }
    if (n.space == "ram") return "(readLE s.mem " + literal(n.offset, arch.addrBytes * 8) + " " + std::to_string(n.size) + ")";
    throw std::runtime_error("unsupported address space " + n.space);
  }
  void line(unsigned indent, const std::string &text) { out << std::string(indent, ' ') << text << '\n'; }
  void write(const Node &n, const std::string &expr, Temps &temps, unsigned indent) {
    if (n.space == "unique") {
      std::string name = "_t" + std::to_string(serial++);
      line(indent, "let " + name + " : BitVec " + std::to_string(n.size * 8) + " := " + expr);
      for (auto it = temps.begin(); it != temps.end();) {
        auto [offset, size] = it->first;
        if (offset < n.offset + n.size && n.offset < offset + size) it = temps.erase(it);
        else ++it;
      }
      temps[{n.offset, n.size}] = name;
    } else if (n.space == "register") {
      const auto &r = reg(n);
      auto value = n.offset == r.offset && n.size == r.size ? expr :
        "insertBits s." + r.name + " " + std::to_string((n.offset - r.offset) * 8) + " " + expr;
      line(indent, "let s := { s with " + r.name + " := " + value + " }");
    } else if (n.space == "ram") {
      line(indent, "let s := { s with mem := writeLE s.mem " + literal(n.offset, arch.addrBytes * 8) + " " +
        std::to_string(n.size) + " " + expr + " }");
    } else throw std::runtime_error("unsupported destination space " + n.space);
  }
  std::string expression(const Op &op, const Temps &temps) const {
    auto a = read(op.in.at(0), temps);
    auto b = [&]() { return read(op.in.at(1), temps); };
    auto binary = [&](const char *symbol) { return "(" + a + " " + symbol + " " + b() + ")"; };
    auto cmp = [&](const std::string &expr) { return "(boolByte " + expr + ")"; };
    auto method = [&](const char *name) { return "(" + a + "." + name + " " + b() + ")"; };
    unsigned width = op.out->size * 8;
    switch (op.code) {
    case CPUI_COPY: return a;
    case CPUI_INT_ZEXT: return "(" + a + ".setWidth " + std::to_string(width) + ")";
    case CPUI_INT_SEXT: return "(" + a + ".signExtend " + std::to_string(width) + ")";
    case CPUI_INT_ADD: return binary("+");
    case CPUI_INT_SUB: return binary("-");
    case CPUI_INT_MULT: return binary("*");
    case CPUI_INT_AND: return binary("&&&");
    case CPUI_INT_OR: return binary("|||");
    case CPUI_INT_XOR: return binary("^^^");
    case CPUI_INT_NEGATE: return "(~~~" + a + ")";
    case CPUI_INT_2COMP: return "(-" + a + ")";
    case CPUI_INT_EQUAL: return cmp(binary("=="));
    case CPUI_INT_NOTEQUAL: return cmp(binary("!="));
    case CPUI_INT_LESS: return cmp(method("ult"));
    case CPUI_INT_LESSEQUAL: return cmp(method("ule"));
    case CPUI_INT_SLESS: return cmp(method("slt"));
    case CPUI_INT_SLESSEQUAL: return cmp(method("sle"));
    case CPUI_INT_CARRY: return cmp("((" + a + " + " + b() + ").ult " + a + ")");
    case CPUI_INT_SCARRY:
      return cmp("((" + a + ".msb == " + b() + ".msb) && ((" + a + " + " + b() + ").msb != " + a + ".msb))");
    case CPUI_INT_SBORROW:
      return cmp("((" + a + ".msb != " + b() + ".msb) && ((" + a + " - " + b() + ").msb != " + a + ".msb))");
    case CPUI_BOOL_NEGATE: return cmp("(" + a + " == 0)");
    case CPUI_BOOL_AND: return cmp("((" + a + " != 0) && (" + b() + " != 0))");
    case CPUI_BOOL_OR: return cmp("((" + a + " != 0) || (" + b() + " != 0))");
    case CPUI_BOOL_XOR: return cmp("((" + a + " != 0) ^^ (" + b() + " != 0))");
    case CPUI_INT_LEFT: return "(shiftLeft " + a + " " + b() + ".toNat)";
    case CPUI_INT_RIGHT: return "(" + a + " >>> " + b() + ".toNat)";
    case CPUI_INT_SRIGHT: return "(" + a + ".sshiftRight " + b() + ".toNat)";
    case CPUI_PIECE: return "(" + a + " ++ " + b() + ")";
    case CPUI_SUBPIECE: return "((" + a + " >>> (" + b() + ".toNat * 8)).setWidth " + std::to_string(width) + ")";
    case CPUI_POPCOUNT: return "(BitVec.ofNat " + std::to_string(width) + " (popcount " + a + "))";
    default: throw std::runtime_error("unsupported p-code operation " + std::string(get_opname(op.code)));
    }
  }
  void jump(uint64_t target, unsigned indent) {
    auto it = labels.find(target);
    if (it == labels.end()) throw std::runtime_error("branch/fallthrough outside instruction boundaries: " + number(target));
    line(indent, "return .inl (.p" + std::to_string(it->second) + ", { s with " + arch.pc + " := " + number(target) + " })");
  }
  void branch(const Insn &insn, size_t index, const Node &dest, Temps temps, unsigned indent) {
    if (dest.space == "ram") { jump(dest.offset, indent); return; }
    if (dest.space != "const") throw std::runtime_error("unsupported branch space");
    // Only forward intra-instruction branches: no hidden micro-loop or duplication explosion.
    unsigned bits = dest.size * 8;
    uint64_t offset = dest.offset;
    if (bits < 64) offset &= (UINT64_C(1) << bits) - 1;
    if (!offset || (offset >> (bits - 1)) || offset > insn.ops.size() - index)
      throw std::runtime_error("backward/out-of-range intra-instruction branch is unsupported");
    body(insn, index + offset, std::move(temps), indent);
  }
  void body(const Insn &insn, size_t index, Temps temps, unsigned indent) {
    if (++emitted > 4096) throw std::runtime_error("instruction expansion exceeds 4096 operations");
    if (index == insn.ops.size()) { jump(insn.address + insn.length, indent); return; }
    const auto &op = insn.ops[index];
    switch (op.code) {
    case CPUI_BRANCH: branch(insn, index, op.in.at(0), temps, indent); return;
    case CPUI_CBRANCH:
      line(indent, "if " + read(op.in.at(1), temps) + " != 0 then");
      branch(insn, index, op.in.at(0), temps, indent + 2);
      line(indent, "else");
      body(insn, index + 1, std::move(temps), indent + 2); return;
    case CPUI_RETURN:
      line(indent, "return .inr { s with " + arch.pc + " := " + read(op.in.at(0), temps) + " }"); return;
    case CPUI_LOAD:
      if (op.space != "ram") throw std::runtime_error("only ram LOAD is supported");
      write(*op.out, "(readLE s.mem " + read(op.in.at(1), temps) + " " + std::to_string(op.out->size) + ")", temps, indent);
      break;
    case CPUI_STORE:
      if (op.space != "ram") throw std::runtime_error("only ram STORE is supported");
      line(indent, "let s := { s with mem := writeLE s.mem " + read(op.in.at(1), temps) + " " +
        std::to_string(op.in.at(2).size) + " " + read(op.in.at(2), temps) + " }");
      break;
    default:
      if (!op.out) throw std::runtime_error("unsupported control/effect " + std::string(get_opname(op.code)));
      write(*op.out, expression(op, temps), temps, indent);
    }
    body(insn, index + 1, std::move(temps), indent);
  }
public:
  Printer(const std::vector<Insn> &code, const std::vector<Reg> &regs, const Arch &arch, std::ostream &out)
    : code(code), regs(regs), arch(arch), out(out) {
    for (size_t i = 0; i < code.size(); ++i) labels[code[i].address] = i;
  }
  void print(const std::string &name, const Image &image) {
    out << "-- Generated by pcode-lean. Raw SLEIGH p-code; no decompiler or GOTO pass.\n"
        << "-- SLEIGH revision: " << PCODE_SLEIGH_REV << "\n-- Bytes at " << number(image.base) << ": ";
    for (auto c : image.bytes) out << std::hex << std::setw(2) << std::setfill('0') << unsigned(c);
    out << std::dec << "\nimport PcodeLean\n\nnamespace " << name << "\nopen PcodeLean\n\ninductive PC where\n";
    for (size_t i = 0; i < code.size(); ++i) out << "  | p" << i << "\n";
    out << "  deriving DecidableEq, Repr\n\nabbrev Frame := PC × " << arch.state << "\n\n"
        << "def step (frame : Frame) : Id (Sum Frame " << arch.state << ") := do\n"
        << "  let s := frame.2\n  match frame.1 with\n";
    for (size_t i = 0; i < code.size(); ++i) {
      out << "  | .p" << i << " =>\n    -- " << number(code[i].address) << " " << code[i].text << "\n";
      serial = emitted = 0;
      try { body(code[i], 0, {}, 4); }
      catch (const std::exception &e) {
        throw std::runtime_error(number(code[i].address) + " " + code[i].text + ": " + e.what());
      }
    }
    out << "\ndef initial (s : " << arch.state << ") : Frame := (.p0, { s with " << arch.pc << " := " << number(image.base) << " })\n"
        << "def run (s : " << arch.state << ") := PcodeLean.run step (initial s)\n"
        << "def execute (fuel : Nat) (s : " << arch.state << ") := PcodeLean.execute step fuel (initial s)\n\nend " << name << '\n';
  }
};

uint64_t integer(const std::string &s) {
  size_t end;
  if (s.empty() || s.front() == '-') throw std::runtime_error("invalid unsigned integer");
  auto n = std::stoull(s, &end, 0);
  if (end != s.size()) throw std::runtime_error("invalid unsigned integer");
  return n;
}
}

int main(int argc, char **argv) {
  try {
    std::string binary, hex, name = "Lifted", sla, pspec, archName = "x86-64";
    uint64_t base = 0x1000;
    for (int i = 1; i < argc; ++i) {
      std::string arg = argv[i];
      if (arg == "--help") {
        std::cout << "pcode-lean (--binary FILE | --hex HEX) [--arch x86-64|riscv32] [--base ADDRESS] [--name NAMESPACE] [--sla FILE --pspec FILE]\n";
        return 0;
      }
      if (++i == argc) throw std::runtime_error("missing option value");
      std::string value = argv[i];
      if (arg == "--binary") binary = value;
      else if (arg == "--hex") hex = value;
      else if (arg == "--base") base = integer(value);
      else if (arg == "--name") name = value;
      else if (arg == "--sla") sla = value;
      else if (arg == "--pspec") pspec = value;
      else if (arg == "--arch") archName = value;
      else throw std::runtime_error("unknown option " + arg);
    }
    auto archIt = std::find_if(ARCHS.begin(), ARCHS.end(), [&](const Arch &a) { return a.name == archName; });
    if (archIt == ARCHS.end()) throw std::runtime_error("unknown architecture " + archName);
    const Arch &arch = *archIt;
    if (sla.empty()) sla = arch.sla;
    if (pspec.empty()) pspec = arch.pspec;
    if (binary.empty() == hex.empty()) throw std::runtime_error("provide exactly one of --binary and --hex");
    if (name.empty() || name == "Type" || name == "Prop" || name == "Sort" ||
        !std::isupper(static_cast<unsigned char>(name[0])) ||
        !std::all_of(name.begin(), name.end(), [](unsigned char c) { return std::isalnum(c) || c == '_'; }))
      throw std::runtime_error("namespace must start with an uppercase letter and contain only letters, digits, underscores");
    std::vector<unsigned char> bytes;
    if (!binary.empty()) {
      std::ifstream input(binary, std::ios::binary);
      if (!input) throw std::runtime_error("cannot read binary " + binary);
      bytes.assign(std::istreambuf_iterator<char>(input), {});
    } else {
      if (hex.size() % 2) throw std::runtime_error("hex bytes must have even length");
      for (size_t i = 0; i < hex.size(); i += 2) {
        if (!std::isxdigit(static_cast<unsigned char>(hex[i])) || !std::isxdigit(static_cast<unsigned char>(hex[i+1])))
          throw std::runtime_error("invalid hex bytes");
        bytes.push_back(static_cast<unsigned char>(std::stoul(hex.substr(i, 2), nullptr, 16)));
      }
    }
    if (bytes.empty() || bytes.size() > 65536 || base > std::numeric_limits<uint64_t>::max() - bytes.size())
      throw std::runtime_error("input must contain 1..65536 bytes without address wraparound");
    Image image(base, std::move(bytes), arch.type);
    AttributeId::initialize();
    ElementId::initialize();
    ContextInternal context;
    Sleigh engine(&image, &context);
    DocumentStorage storage;
    std::istringstream config("<sleigh>" + sla + "</sleigh>");
    storage.registerTag(storage.parseDocument(config)->getRoot());
    storage.registerTag(storage.openDocument(pspec)->getRoot());
    engine.initialize(storage);
    engine.allowContextSet(false);
    XmlDecode decoder(&engine, storage.getTag("processor_spec"));
    auto root = decoder.openElement();
    while (auto child = decoder.peekElement()) {
      if (child == ELEM_CONTEXT_DATA) { context.decodeFromSpec(decoder); break; }
      decoder.openElement(); decoder.closeElementSkipping(child);
    }
    decoder.closeElement(root);
    if (engine.isBigEndian() || engine.getDefaultCodeSpace()->getAddrSize() != arch.addrBytes ||
        engine.getDefaultCodeSpace()->getWordSize() != 1 ||
        (arch.name == "x86-64" &&
         context.ContextDatabase::getVariable("longMode", Address(engine.getDefaultCodeSpace(), base)) != 1))
      throw std::runtime_error("only little-endian " + arch.name + " with byte addresses is supported" +
        (arch.name == "x86-64" ? " (long mode)" : ""));
    std::vector<Reg> regs;
    for (std::string name : arch.regs) {
      auto r = engine.getRegister(name);
      unsigned expected = arch.name == "x86-64" && name.size() == 2 && name[0] != 'R' ? 1 : arch.addrBytes;
      if (static_cast<unsigned>(r.size) != expected) throw std::runtime_error("incompatible " + arch.name + " register layout");
      std::transform(name.begin(), name.end(), name.begin(), [](unsigned char c) { return std::tolower(c); });
      regs.push_back({name, r.offset, static_cast<unsigned>(r.size)});
    }
    std::vector<Insn> instructions;
    for (uint64_t address = base; address < base + image.bytes.size();) {
      Capture capture;
      Assembly assembly;
      Address pc(engine.getDefaultCodeSpace(), address);
      int length = engine.oneInstruction(capture, pc);
      if (length <= 0 || static_cast<uint64_t>(length) > base + image.bytes.size() - address)
        throw std::runtime_error("truncated instruction at " + number(address));
      engine.printAssembly(assembly, pc);
      // SLEIGH can lower call-to-next-address into just a stack write and fallthrough.
      // Reject calls too: this version stops at the first machine RETURN. On RISC-V a jal/jalr
      // that links nothing (rd = zero) is a jump or return, not a call.
      bool links = std::find(arch.calls.begin(), arch.calls.end(), assembly.mnemonic) != arch.calls.end();
      if (links && arch.name == "riscv32") links = assembly.text.find("zero") == std::string::npos;
      if (links) throw std::runtime_error("call is unsupported at " + number(address) + ": " + assembly.text);
      instructions.push_back({address, static_cast<unsigned>(length), assembly.text, std::move(capture.ops)});
      address += length;
    }
    // Buffer the complete result: unsupported input never leaves a plausible partial model on stdout.
    std::ostringstream generated;
    Printer(instructions, regs, arch, generated).print(name, image);
    std::cout << generated.str();
    return 0;
  } catch (const LowlevelError &e) { std::cerr << "pcode-lean: " << e.explain << '\n'; }
    catch (const std::exception &e) { std::cerr << "pcode-lean: " << e.what() << '\n'; }
  return 1;
}
