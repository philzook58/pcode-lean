# Checkpoint: x86 contracts

Checkpoint date: 2026-10-25. Annotated tag: `checkpoint-x86-contracts`.

## Verified scope

The x86 examples have checked model contracts for arithmetic, memory effects,
register and flag preservation, return behavior, and termination. Caller helpers
cover separate buffers, exact in-place addition, empty fills, and stack scratch.
The stack spill has a 32-byte bound at every instruction boundary when subtraction
cannot underflow; the 256-byte reservation is proved to violate that bound.

The checkpoint passed regeneration checks, the Lean build and axiom audit,
unsupported-input checks, and 601 native/model comparisons. The audit uses only
standard axioms. Recheck with:

```sh
cmake --build build --target pcode-lean -j3
ctest --test-dir build --output-on-failure
```

See [README.md](README.md) for a fresh build and [the walkthrough](docs/WRITES.md)
for contract assumptions. Build outputs and caches are ignored; generated Lean
fixtures, handwritten proofs, and dependency pins are tracked.

## Known limits

These proofs establish properties of the lifted model, not a certified lift or
ISA equivalence. The auxiliary-carry regression deliberately remains visible:
the AF-dependent example returns 2 in the model and 18 natively.

RV32 state and frontend scaffolding are experimental. The checked example and
native comparison suite covers x86; it does not validate RV32 support. Memory is
a total byte array without permissions, faults, MMIO, or concurrency.

## Next task when resuming

Prove a small assembly caller using an existing routine's contract, beginning
with a call to `inc64`. Compose the helper summary with the caller's proof rather
than unfolding its body. Check argument/result transfer, caller- and callee-saved
registers, stack restoration, the return cell, and the stack bound across the call.
Add only the direct-call support needed for this example, and compare the exact
fixture with native execution. Keep C/RTL correspondence and wider ISA coverage
for later work.
