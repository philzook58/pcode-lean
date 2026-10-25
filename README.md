# pcode-lean

[Checkpoint status and next task](STATUS.md) · Git tag: `checkpoint-x86-contracts`.

Lift a small x86-64 code region through Trail of Bits' standalone SLEIGH C++ library,
emit ordinary executable Lean, and prove contracts with Lean's `vcgen` framework.

```text
instruction bytes → raw SLEIGH p-code → Lean BitVec code → handwritten contract + proof
                                                 ↘ concrete execution
```

This is a fresh prototype. It does not depend on `lean-pcode`, `lean-sleigh`, ASMC,
CBMC, GOTO, or Mathlib. The Lean library depends only on Lean/Std. The C++ tool
links `sleigh::sla`; its target builds x86-64 and experimental RV32 specifications.
The verified examples and native validation suite cover x86-64.

## First examples

[Original assembly](examples/routines.S) and [separate proofs](Examples/Proofs.lean):

| Routine | Universal model contract | Completion |
| --- | --- | --- |
| `inc64` | Returns `rdi + 1` modulo 2⁶⁴ | Two instructions |
| `umax64` | Returns the unsigned maximum of `rdi` and `rsi` | Four instructions, including a conditional move |
| `count64` | Counts down `rdi`, returning the original count | A manual invariant and natural-number rank, for every 64-bit count |
| `scan64` | ORs an arbitrary number of 64-bit memory limbs, preserving memory | Manual suffix invariant and rank |
| `add128` | Adds two register pairs, including the carry beyond 128 bits | Five instructions |

Each contract also proves the eight-byte stack adjustment, the return destination
loaded from the original stack, and preservation of data memory. These statements
allow arbitrary initial register and memory values; a caller must additionally
establish that the modeled return address and stack represent its actual execution.
They do not claim to cover every architectural effect or ABI obligation.

[Combined contracts](Examples/Contracts.lean) now also prove explicit register,
flag, and memory frames for all five routines. The frames identify permitted
clobbers and preserve everything else. System V caller-saved summaries are
available separately. [The checked tutorial](docs/TUTORIAL.md) explains output
byte ranges, caller-owned memory, stack scratch, and return-cell nonoverlap.
The adder uses a register interface returning RAX, RDX, and CF; it does not write
an output buffer or claim to implement a C calling convention for a 129-bit result.

[Memory-writing examples](docs/WRITES.md) now add a two-limb output-buffer adder,
a fill loop, and a 32-byte stack spill. Their proofs specify exact memory effects,
preserved registers, return-cell nonoverlap, and completion. A fourth fixture
shows why an exit frame alone cannot establish maximum stack depth. The new
[caller helpers](Examples/Callers.lean) discharge bytewise obligations using buffer
endpoints, support exact in-place addition, and remove the fixed spill's return-cell
premise. [Stack bounds](Examples/StackBounds.lean) prove a 32-byte limit at every
instruction boundary and reject the 256-byte reservation. The tests compare whole
buffers and carries against native execution and a byte reference.

```lean
import Examples
open PcodeLean Std.WP Examples

example (s : X86State) :
    ⦃True⦄ Count.run s ⦃fun out ↦ Returns s out s.rdi⦄ :=
  CountProof.correct s
```

`run` means partial correctness over every finite execution prefix. Termination
is a separate theorem: `CountProof.terminates` establishes a successful execution
within `3 * s.rdi.toNat + 5` instruction steps. Concrete fuel exhaustion returns
`none` and the command-line runner reports failure. A proof never treats exhaustion
as successful termination.

## Build and check

[GitHub Actions](https://github.com/philzook58/pcode-lean/actions/workflows/ci.yml)
runs the Lean proofs and the full native integration suite on x86-64 Ubuntu for
pushes and pull requests. It uses the pinned toolchain and fetches the CMake
dependencies afresh, without sibling checkout paths or cached native binaries.

Requires Lean/Lake **4.35.0**, C++17, CMake 3.24+, Ninja, zlib development headers,
and Git. Example regeneration and tests additionally use Python 3, a C compiler,
and GNU binutils (`objcopy`, `readelf`). Native validation requires x86-64 Linux
and a GCC/Clang-compatible compiler.

```sh
cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release
cmake --build build --target pcode-lean -j3
python3 tools/generate.py
lake build
ctest --test-dir build --output-on-failure
```

CMake pins SLEIGH at `bfe2771eb304c2b4f01c2fa61f5342be54a91906`, whose stable
dependency is Ghidra **12.1.4** plus the wrapper's patches. SLEIGH's source build
downloads Ghidra; building one language does not make that download small.
To reuse matching existing source downloads, pass
`-DFETCHCONTENT_SOURCE_DIR_SLEIGH=/absolute/path/to/sleigh` and
`-DFETCHCONTENT_SOURCE_DIR_GHIDRASOURCE=/absolute/path/to/ghidra` at configure time.
Those overrides must match the pinned sources and patches. This checkout was
validated using the matching source caches in the sibling ASMC build; it does
not link ASMC or CBMC.

Small generated models are checked in for inspection. `python3 tools/generate.py
--check` rejects stale output without rewriting it. Regeneration never changes
the handwritten proofs. The tests rebuild proofs and audit their axioms.

For a self-contained code region:

```sh
build/pcode-lean --hex 488d4701c3 --base 0x1000 --name Increment > build/Increment.lean
```

`--binary FILE` accepts raw bytes instead of hex. The base is the actual address
at which those bytes are modeled. The initial entry is the first byte; every
instruction in the region is decoded. There is no ELF loader, relocation pass,
function discovery, or source-C compiler in this first version. Extract and
relocate bytes before lifting. `--sla` and `--pspec` can select matching external
specifications; these are trusted inputs, and the generated build-revision
comment alone does not authenticate custom specs.

## Semantics and limits

The exporter emits one Lean block per machine instruction. Arithmetic is normal
`BitVec` code; raw p-code `unique` temporaries become local typed `let` bindings.
There is no second expression language or general p-code interpreter inside Lean.
Forward intra-instruction branches become Lean conditionals. Machine branches
retain an explicit finite PC type, making manual invariants straightforward.
Register aliases use slices of canonical register cells, including SLEIGH's
explicit zero-extension on x86 32-bit writes. `RET` executes its actual stack load
and stack update before producing the final state.
Execution stops at the first machine return; its contract must establish the
intended external return destination. Calls and return-oriented internal control
flow are outside this first version.

The initial subset includes scalar integer/boolean arithmetic and comparisons,
carry/overflow calculations, shifts, extensions, concatenation/extraction,
population count, flat little-endian loads/stores, direct branches, forward
p-code branches, and returns. Varnodes are limited to 1–8 bytes. Unsupported
operations, spaces, registers, calls, non-return indirect jumps, backward p-code
branches, invalid control-flow boundaries, and truncated instructions fail.
The complete output is buffered, so rejection emits no partial Lean model.
Translation accepts a subset; the native tests exercise the examples and probes,
not every possible instruction that happens to use these p-code operations.

Memory is a total function from 64-bit addresses to bytes. There are no access
permissions, allocation objects, exceptions, page translation, MMIO, concurrency,
or timing effects. Code is fixed separately from data memory: applications must
exclude self-modifying code. Incoming flag cells use p-code's boolean encoding.
The prototype is for small user-mode routines under these assumptions.

## The trust gap is observable

Lean checks the theorem about the emitted model. Instruction decoding, SLEIGH's
instruction definitions, this exporter, and correspondence of the flat memory
model to the execution environment remain trusted. A contract proof does not
close those gaps.

`afgap64` deliberately demonstrates a known gap in the pinned x86 semantics:
after adding one to `AL = 15`, `LAHF` observes auxiliary carry on the CPU. Native
execution returns **18**; the lifted model returns **2**. The validation suite
requires that exact discrepancy to remain visible. This example has no theorem
claiming native correctness. AF is excluded explicitly from the separate defined-
flag comparisons for the verified examples; a property depending on AF needs
additional semantics work. Undefined flags are not a basis for equivalence claims.

Tests compare the exact fixture instructions with native execution, including
defined CF/PF/ZF/SF/OF where appropriate. Extra native probes exercise low/high
register aliases, 32-bit zero-extension, stack memory, and masked shift counts.
These tests can expose a lifting error but are not a proof of ISA fidelity.
Ghidra's [emulator](https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/emulate.cc)
and [operation behaviors](https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/opbehavior.cc)
are useful translation references; they share the instruction definitions and
therefore would not be an independent ISA oracle.

## Where this could go

[Related work and concrete lessons](docs/RELATED_WORK.md) examines s2n-bignum's
HOL Light contracts, HOL4 certified decompilation/HolBA, and Isabelle x86/IsaBIL
verification. It records proposed follow-ups separately from implemented features.

The read-only limb scan, two-limb register adder, and explicit frame contracts
are implemented, together with memory-output addition, fill, and a stack spill.
Caller helpers and instruction-boundary stack bounds are also implemented.
Cross-tool correspondence and lift certification remain follow-ups.
ASMC can optionally find bounded counterexamples on the same bytes; it is not a dependency or a source of Lean proof certificates.

For C/assembly/RTL correspondence, start by proving each imported implementation
implements the same small bitvector specification. C-side preconditions must
exclude undefined behavior. Hardware relations can then account for latency or
instruction retirement explicitly, rather than equating one CPU instruction
with one RTL clock. A common universal IR is not needed for the first example.

Sail is a useful independent architectural reference, especially for RISC-V:
the [official model has a Lean emulator](https://github.com/riscv/sail-riscv/tree/master/lean_emulator).
The [Sail project](https://github.com/rems-project/sail#readme) describes its x86
models as user-mode fragments, so selecting Sail still requires checking coverage
for the intended instructions. A later instruction-level refinement theorem
could connect a supported p-code subset to a stronger ISA reference. That is a
separate claim from the contracts already checked here.

Dependency attribution and reference links: [THIRD_PARTY.md](THIRD_PARTY.md).

# AI Disclosure
This code is heavily AI produced
