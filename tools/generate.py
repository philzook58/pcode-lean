#!/usr/bin/env python3
"""Assemble the original fixtures and regenerate their direct Lean models."""
import argparse
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ROUTINES = {"inc64": "Increment", "umax64": "Maximum", "count64": "Count", "afgap64": "AFGap",
            "scan64": "Scan", "add128": "Add128", "addmem": "AddMem",
            "fill64": "Fill", "stack32": "Stack32", "reserve256": "Reserve256"}


def run(args):
    result = subprocess.run(list(map(str, args)), capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f"command failed: {args}\n{result.stdout}{result.stderr}")
    return result.stdout


def generate(lifter, check=False):
    build = ROOT / "build"
    build.mkdir(exist_ok=True)
    obj = build / "routines.o"
    run(["cc", "-c", ROOT / "examples/routines.S", "-o", obj])
    # No relocations are allowed in these standalone code regions.
    relocations = run(["readelf", "-r", obj])
    if "There are no relocations" not in relocations:
        raise RuntimeError("fixture code must be self-contained: " + relocations)
    directory = ROOT / "Examples/Generated"
    directory.mkdir(parents=True, exist_ok=True)
    for routine, namespace in ROUTINES.items():
        binary = build / f"{routine}.bin"
        run(["objcopy", "-O", "binary", "--only-section=.text." + routine, obj, binary])
        text = run([lifter, "--binary", binary, "--name", namespace])
        target = directory / f"{namespace}.lean"
        if check:
            if not target.exists() or target.read_text() != text:
                raise RuntimeError(f"stale generated model: {target}")
        else:
            target.write_text(text)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lifter", type=Path, default=ROOT / "build/pcode-lean")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    generate(args.lifter.resolve(), args.check)
