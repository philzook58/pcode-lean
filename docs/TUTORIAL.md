# Contracts for callers, buffers, and stack memory

This walkthrough follows the progression in s2n-bignum's
[x86 tutorial](https://github.com/awslabs/s2n-bignum/tree/main/x86/tutorial):
computation, memory, loops, then multiword specifications. Its
[memory example](https://github.com/awslabs/s2n-bignum/blob/main/x86/tutorial/memory.ml)
is particularly useful for understanding frame conditions and nonoverlap.
The Lean examples here are original; no HOL Light proof is imported.

The snippets below use `import Examples`. The worked caller and store proofs
are compiled in [Examples/Tutorial.lean](../Examples/Tutorial.lean).

## 1. State what a routine computes and what it may change

`Examples.Contracts.increment` combines the arithmetic specification with a frame.
The separate `IncrementProof.terminates` proves completion. Likewise, `maximum`,
`count`, `scan`, and `add128` have combined contracts. The last two also have
`scan_terminates` and `add128_terminates`, which return a witness satisfying both
the functional specification and frame.

`MayChange allowed before after` means:

* Every register outside `allowed.registers` retains its original value.
* Every flag outside `allowed.flags` retains its original value.
* Every byte outside `allowed.memory` retains its original value.

It describes the relation between entry and exit states. It does not say every
permitted location changed, nor prohibit temporary writes that are later undone.
It is not an access-permission or memory-safety assertion.

Our per-routine footprints are narrower than the calling convention. Increment
and maximum may change RAX, RSP, RIP, and arithmetic flags; count additionally
clobbers RDI, scan additionally clobbers RDI and RSI, and add128 clobbers RDX.
All five preserve every data-memory byte. The frame also preserves DF.

`sysVFootprint` permits System V AMD64 caller-saved registers, RSP, RIP, arithmetic
flags, and a supplied memory predicate. The proved `Frames.*Frame.sysV` summaries
widen the corresponding narrow footprints. They preserve RBX, RBP, R12–R15,
and DF. A full native ABI claim additionally needs environment assumptions such
as a correctly initialized stack and DF being clear on entry.

## 2. Extract the caller's facts

The checked `Tutorial.increment_caller` derives three facts from the combined
contract: RAX contains the increment, RBX is unchanged, and the byte at entry
RSP+8 is unchanged. This illustrates that callers can use a small consequence
of a contract without unfolding the generated p-code.

`StackReturn before after` separately states that RSP advances by eight bytes and
RIP receives the address stored in the original return cell. A frame permitting
RSP to change would not establish that adjustment on its own.

## 3. Describe output bytes and protect everything else

`ByteRegion dst bytes p` is a modular byte interval: the unsigned distance from
`dst` to `p` is less than `bytes`. Wrapped addresses are supported explicitly.
`writeLE_inside` gives the exact byte representation written in that interval;
`writeLE_outside` proves equality with the previous memory elsewhere.
`writeLE_mayChange` packages that behavior as a frame with no register clobbers.

The checked `Tutorial.store_and_keep_return` takes a disjointness assumption
between the output region and the return-cell bytes. It proves both the store's
frame and preservation of the return address. `ReadRegion` describes the exact
byte addresses a little-endian load reads; `readLE_frame` preserves a load when
its bytes lie outside the write footprint.

`StackScratch entryRSP size` describes a candidate scratch interval below entry
RSP. `Tutorial.bufferAndScratch` shows how to permit an output buffer and stack
scratch together. The caller must reserve that space and establish needed
nonoverlap; declaring scratch does not allocate memory or establish an ABI red
zone. `MayChange.compose` combines two summaries by taking the union of their
allowed registers, flags, and memory regions. Restoring a saved register must
still be proved if the overall contract promises its preservation.

## 4. A read-only limb scan

`ScanProof.limbOr mem base n` is a recursive specification for OR-ing `n`
little-endian 64-bit limbs. `scan64` implements it with a loop. Its invariant
relates the accumulated OR to the remaining memory suffix. Its rank proves
completion within `4 * n + 5` instructions for every 64-bit count.

The theorem is about total flat memory, so it permits modular addresses and
does not prove that the input buffer is mapped on a real machine. For native
use, the caller must supply a readable input region. The scan never writes it.

## 5. Two limbs and the carry bit

`add128` accepts `(RSI:RDI)` and `(RCX:RDX)` and returns `(RDX:RAX)` with carry
in CF. This is a small register interface, not a C ABI for returning 129 bits.
Its exact natural-number theorem is:

```text
RAX_out + 2^64 * RDX_out + 2^128 * CF_out
  = (RDI_in + 2^64 * RSI_in) + (RDX_in + 2^64 * RCX_in)
```

`Contracts.add128_value` derives that equation from the routine's postcondition.
The proof uses elementary carry lemmas and natural-number arithmetic; it adds
no native-evaluation axioms. The routine completes in five instructions and
preserves data memory. The [memory-output adder](WRITES.md) reuses this arithmetic
proof and adds exact store, aliasing, and frame contracts.

## 6. Use buffer endpoints and check the stack throughout execution

`Callers.add` accepts an exact output/input alias or a `Separated` premise for each
16-byte input. `Callers.fill` accepts separation between the return cell and the
whole output buffer. These wrappers derive the bytewise conditions automatically;
[checked caller examples](../Examples/CallerChecks.lean) demonstrate left/right
in-place addition, separate output, and a zero-length fill inside the return cell.

`Callers.stack_safe s hs` combines the spill's exact exit contract with its bound
at every instruction boundary. Its only premise is `hs : 32 ≤ s.rsp.toNat`, which
prevents subtraction underflow. The return-cell disjointness fact is automatic.
The working RSP stays between entry−32 and entry, and RET advances it to entry+8.
`StackBounds.reserve256_exceeds32` rejects that same bound for the larger reservation,
even though its exit frame holds. These trace observations are distinct from both
termination and memory access permissions. See [the detailed walkthrough](WRITES.md).

## Check the whole walkthrough

Run `lake build`, then `ctest --test-dir build --output-on-failure`.
Validation regenerates models, audits theorem axioms, checks rejected inputs,
and compares the limb examples with both native execution and Python integers.
Negative frame checks reject callee-saved clobbers, undeclared writes, and a
missing return stack adjustment.

All contracts remain relative to the lifted model. The known auxiliary-carry
gap and the distinction between model proofs and ISA fidelity still apply.
