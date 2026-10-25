#!/usr/bin/env python3
"""Regeneration, kernel proofs, rejection cases, and an independent native x86 oracle."""
import argparse
from pathlib import Path
import platform
import random
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from generate import generate
from check_bignum import check_bignum
from check_writes import check_writes


def run(args, *, data=None, expected=0):
    result = subprocess.run(list(map(str, args)), cwd=ROOT, input=data,
                            capture_output=True, text=True, timeout=60)
    if result.returncode != expected:
        raise RuntimeError(f"{args}: exit {result.returncode}\n{result.stdout}{result.stderr}")
    return result


def native_rows(routine, pairs):
    text = run([ROOT / "build/native", routine], data="".join(f"{a} {b}\n" for a, b in pairs)).stdout
    rows = [tuple(map(int, line.split())) for line in text.splitlines()]
    assert len(rows) == len(pairs) and all(len(row) == 2 for row in rows), "incomplete native output"
    return rows


def lean_row(routine, a, b, fuel=2000):
    text = run([ROOT / ".lake/build/bin/pcode-run", routine, a, b, fuel]).stdout
    row = tuple(map(int, text.split()))
    assert len(row) == 4 and row[1:3] == (0x8008, 0x9000), "wrong stack/return state"
    return row


def probes(lifter, pairs):
    obj = ROOT / "build/probes.o"
    run(["cc", "-c", ROOT / "tests/probes.S", "-o", obj])
    assert "There are no relocations" in run(["readelf", "-r", obj]).stdout
    models = []
    for routine, name in [("alias64", "Alias"), ("stack64", "Stack"), ("shift64", "Shift")]:
        binary = ROOT / "build" / f"{routine}.bin"
        run(["objcopy", "-O", "binary", "--only-section=.text." + routine, obj, binary])
        text = run([lifter, "--binary", binary, "--name", name]).stdout
        models.append(text.replace("import PcodeLean\n", ""))
    source = "import PcodeLean\n" + "\n".join(models)
    source += "\ndef main : IO Unit := do\n"
    source += "  let samples : List (Nat × Nat) := [" + ",".join(f"({a},{b})" for a, b in pairs) + "]\n"
    source += """  for (a, b) in samples do
    let s : PcodeLean.X86State := {
      rdi := BitVec.ofNat 64 a
      rsi := BitVec.ofNat 64 b
      rsp := 0x8000
      mem := PcodeLean.writeLE (fun _ ↦ 0) 0x8000 8 0x9000 }
    for execute in [Alias.execute, Stack.execute, Shift.execute] do
      let some out := execute 20 s | throw (IO.userError "probe exhausted fuel")
      if out.rsp != 0x8008 || out.rip != 0x9000 then
        throw (IO.userError "probe damaged return state")
      IO.println out.rax.toNat
"""
    path = ROOT / "build/Probes.lean"
    path.write_text(source)
    values = list(map(int, run(["lake", "env", "lean", "--run", path]).stdout.split()))
    assert len(values) == 3 * len(pairs), "incomplete Lean probe output"
    for index, routine in enumerate(["alias", "stack", "shift"]):
        expected = native_rows(routine, pairs)
        for pair, actual, (reference, _) in zip(pairs, values[index::3], expected):
            assert actual == reference, (routine, pair, actual, reference)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lifter", type=Path, default=ROOT / "build/pcode-lean")
    args = parser.parse_args()
    lifter = args.lifter.resolve()
    generate(lifter, check=True)
    print("Generated models match the current assembly and lifter.", flush=True)
    run(["lake", "build"])
    audit = ROOT / "build/Audit.lean"
    names = ["Examples.IncrementProof.correct", "Examples.IncrementProof.terminates",
             "Examples.MaximumProof.correct", "Examples.MaximumProof.terminates",
             "Examples.CountProof.correct", "Examples.CountProof.terminates",
             "PcodeLean.execute_correct", "PcodeLean.finishes_of_rank",
             "Examples.Contracts.scan", "Examples.Contracts.scan_terminates",
             "Examples.Contracts.add128", "Examples.Contracts.add128_terminates",
             "Examples.Contracts.add128_value", "Examples.Contracts.increment",
             "Examples.Contracts.maximum", "Examples.Contracts.count",
             "PcodeLean.MayChange.compose", "PcodeLean.readLE_frame",
             "Examples.FrameChecks.store_contract", "Examples.FrameChecks.return_cell_preserved",
             "Examples.Tutorial.increment_caller", "Examples.Tutorial.store_and_keep_return",
             "Examples.WriteProof.add_completion", "Examples.WriteProof.add_correct",
             "Examples.WriteProof.stack_completion", "Examples.WriteProof.stack_correct",
             "Examples.WriteProof.reserve_completion", "Examples.WriteProof.reserve_depth",
             "Examples.FillProof.completion", "Examples.FillProof.terminates",
             "Examples.FillProof.memory_frame", "Examples.FillProof.caller_contract",
             "PcodeLean.Separated.read_write", "PcodeLean.stack_scratch_separated",
             "PcodeLean.ReadRegion.high_limb", "PcodeLean.always_invariant",
             "PcodeLean.Always.post", "Examples.Callers.add", "Examples.Callers.fill",
             "Examples.Callers.stack_safe", "Examples.StackBounds.stack32",
             "Examples.StackBounds.reserve256_exceeds32", "Examples.CallerChecks.inplace_left",
             "Examples.CallerChecks.inplace_right", "Examples.CallerChecks.separate_output",
             "Examples.CallerChecks.empty_fill_at_return", "Examples.CallerChecks.bounded_spill"]
    audit.write_text("import Examples\n" + "\n".join("#print axioms " + name for name in names) + "\n")
    output = run(["lake", "env", "lean", audit]).stdout
    assert len(output.splitlines()) == len(names), "missing axiom audit output"
    for axioms in re.findall(r"axioms: \[([^]]*)\]", output):
        assert set(axioms.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}, output
    print("Universal contracts and termination proofs pass; only standard axioms.", flush=True)
    rejects = [(["--hex", "48"], None), (["--hex", "0f0bc3"], "CALLOTHER"),
               (["--hex", "eb7f"], "outside"), (["--hex", "90"], "outside"),
               (["--hex", "e800000000c3"], "CALL"), (["--hex", "zz"], "hex"),
               (["--hex", "c3", "--name", "X;Bad"], "namespace"),
               (["--hex", "c3", "--name", "Type"], "namespace"),
               (["--hex", "c3", "--base", "0xffffffffffffffff"], "wraparound")]
    for options, message in rejects:
        result = run([lifter, *options], expected=1)
        assert not result.stdout and result.stderr, "rejected input emitted a partial model"
        assert message is None or message in result.stderr, result.stderr
    exhausted = run([ROOT / ".lake/build/bin/pcode-run", "count", 20, 0, 2], expected=1)
    assert "fuel exhausted" in exhausted.stderr and not exhausted.stdout
    print("Unsupported input and fuel exhaustion fail explicitly.", flush=True)
    if platform.machine() != "x86_64":
        raise RuntimeError("native validation requires an x86-64 host")
    run(["cc", "-O2", "-mno-red-zone", "-fcf-protection=none", ROOT / "tests/native.c",
         ROOT / "examples/routines.S", ROOT / "tests/probes.S", "-o", ROOT / "build/native"])
    rng = random.Random(0xC0DE)
    mask = (1 << 64) - 1
    edge = [0, 1, 15, 16, 127, 128, 255, 256, (1 << 63) - 1, 1 << 63, mask]
    pairs = [(a, b) for a in edge for b in [0, 1, mask]]
    pairs += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(32)]
    count_pairs = [(n, 0) for n in [*range(25), 63, 127, 255, 511]]
    for routine, samples in [("inc", pairs), ("max", pairs), ("count", count_pairs)]:
        for (a, b), (result, flags) in zip(samples, native_rows(routine, samples)):
            model = lean_row(routine, a, b)
            assert model[0] == result, (routine, a, b, model, result)
            if routine != "inc":
                # CF/PF/ZF/SF/OF are defined here. AF is an explicitly recorded SLEIGH gap.
                assert (model[3] & 0x8C5) == (flags & 0x8C5), (routine, a, b, model[3], flags)
    probe_pairs = pairs + [(0x123456789ABCDEF0, n) for n in [31, 32, 63, 64, 65, 255]]
    probes(lifter, probe_pairs)
    model = lean_row("afgap", 0, 0)[0]
    native = native_rows("afgap", [(0, 0)])[0][0]
    assert (model, native) == (2, 18), ("auxiliary-carry witness changed; investigate", model, native)
    cases = 2 * len(pairs) + len(count_pairs) + 3 * len(probe_pairs)
    print(f"{cases} native/model comparisons pass, including defined flags, aliases, stack memory, and shifts.")
    print("Known gap reproduced separately: AF-dependent routine returns model=2, native=18.")
    check_bignum()
    check_writes()


if __name__ == "__main__":
    main()
