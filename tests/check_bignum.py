"""Independent native and mathematical checks for the proved limb examples."""
from pathlib import Path
import random
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def run(args, data=None):
    r = subprocess.run(list(map(str, args)), cwd=ROOT, input=data, text=True,
                       capture_output=True, timeout=60)
    if r.returncode:
        raise RuntimeError(f"{args}\n{r.stdout}{r.stderr}")
    return r.stdout


def check_bignum():
    rng = random.Random(0xADC)
    mask = (1 << 64) - 1
    edge = [0, 1, (1 << 63) - 1, 1 << 63, mask - 1, mask]
    adds = [(a, b, c, d) for a in edge for b in [0, mask] for c in [0, 1, mask] for d in [0, mask]]
    adds += [tuple(rng.getrandbits(64) for _ in range(4)) for _ in range(64)]
    scans = [[], [0], [mask], [0, 0, 0], [0, 1, 0], [mask, mask]]
    scans += [[rng.getrandbits(64) for _ in range(n)] for n in range(2, 33)]
    run(["cc", "-O2", "-mno-red-zone", "-fcf-protection=none", "tests/native_bignum.c",
         "examples/routines.S", "-o", "build/native-bignum"])
    inputs = "".join("add " + " ".join(map(str, row)) + "\n" for row in adds)
    inputs += "".join("scan " + str(len(row)) + " " + " ".join(map(str, row)) + "\n" for row in scans)
    native = [tuple(map(int, line.split())) for line in run(["build/native-bignum"], inputs).splitlines()]
    source = "import Examples\nopen PcodeLean\ndef main : IO Unit := do\n"
    source += "  let adds : List (Nat × Nat × Nat × Nat) := [" + ",".join(
        "(" + ",".join(map(str, row)) + ")" for row in adds) + "]\n"
    source += """  for (a,b,c,d) in adds do
    let s : X86State := {
      rdi := BitVec.ofNat 64 a
      rsi := BitVec.ofNat 64 b
      rdx := BitVec.ofNat 64 c
      rcx := BitVec.ofNat 64 d
      rbx := 0xdeadbeef
      rbp := 0x1234
      r12 := 12
      r13 := 13
      r14 := 14
      r15 := 15
      rsp := 0x8000
      mem := writeLE (fun _ ↦ 0xa5) 0x8000 8 0x9000 }
    let some out := Add128.execute 5 s | throw (IO.userError "add fuel")
    if out.rsp != 0x8008 || out.rip != 0x9000 || out.rbx != s.rbx || out.r15 != s.r15 then
      throw (IO.userError "add frame")
    IO.println s!"{out.rax.toNat} {out.rdx.toNat} {out.cf.toNat}"
"""
    source += "  let scans : List (List Nat) := [" + ",".join(
        "[" + ",".join(map(str, row)) + "]" for row in scans) + "]\n"
    source += """  for words in scans do
    let mut mem := writeLE (fun _ ↦ 0xa5) 0x8000 8 0x9000
    for (word, i) in words.zipIdx do
      mem := writeLE mem (0x6000 + BitVec.ofNat 64 (8 * i)) 8 (BitVec.ofNat 64 word)
    let s : X86State := {
      rdi := BitVec.ofNat 64 words.length
      rsi := 0x6000
      rbx := 0xdeadbeef
      r15 := 15
      rsp := 0x8000
      mem := mem }
    let some out := Scan.execute (4 * words.length + 5) s | throw (IO.userError "scan fuel")
    if out.rsp != 0x8008 || out.rip != 0x9000 || out.rbx != s.rbx || out.r15 != s.r15 then
      throw (IO.userError "scan frame")
    for p in [0, 0x6000, 0x6100, 0x7ff8, 0x8000, 0x8008, 0xffffffffffffffff] do
      if out.mem p != s.mem p then throw (IO.userError "scan memory")
    IO.println out.rax.toNat
"""
    path = ROOT / "build/BignumCases.lean"
    path.write_text(source)
    model = [tuple(map(int, line.split())) for line in run(["lake", "env", "lean", "--run", path]).splitlines()]
    assert len(model) == len(native) == len(adds) + len(scans), "incomplete observations"
    assert model == native, "native/model disagreement"
    for (a, b, c, d), (lo, hi, carry) in zip(adds, model):
        total = a + (b << 64) + c + (d << 64)
        assert lo + (hi << 64) + (carry << 128) == total
    for words, (actual,) in zip(scans, model[len(adds):]):
        expected = 0
        for word in words:
            expected |= word
        assert actual == expected
    print(f"{len(model)} additional native/model/math comparisons pass for scan and 128-bit carry.")


if __name__ == "__main__":
    check_bignum()
