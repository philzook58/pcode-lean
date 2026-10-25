# Writing memory and using stack scratch

The new fixtures exercise three patterns suggested by the sibling ASMC and
goto-lean projects. They are small local examples, generated directly through
SLEIGH, with handwritten Lean proofs. They add no runtime dependencies.

## Two-limb memory addition

`addmem(out, left, right)` reads two little-endian 128-bit values, writes their
sum modulo 2¹²⁸, and returns the carry in RAX. The fixture deliberately reads the
high inputs after storing the low output. Its
[`add_correct`](../Examples/WriteProofs.lean) contract therefore requires:

* The first eight output bytes do not overlap either high input limb.
* Neither output store overlaps the eight-byte return cell.

The first condition admits exact in-place addition (`out = left` or `out = right`).
It does not admit every partial overlap. The contract describes the exact final
memory as two little-endian stores of `Add128Proof.low` and `Add128Proof.high`;
the existing `Add128Proof.arithmetic` theorem establishes their integer meaning
and the carry. Reusing it avoids a second carry proof.

Only RAX, RSP, RIP, arithmetic flags, and the sixteen output bytes may change.
Everything else, including callee-saved registers, is preserved. Successful
completion takes nine instruction steps. Address arithmetic is modular; the
nonoverlap hypotheses describe actual byte addresses, including wraparound.

## Fill loop

[`FillProofs.lean`](../Examples/FillProofs.lean) proves completion for every 64-bit
count within `4 * count + 3` steps, including zero. `fillMemory` specifies the
exact sequence of eight-byte stores. `Writes` describes their union, so the memory
frame does not need a separate arithmetic theorem about large address ranges.

`caller_contract` combines this exact memory result with preservation outside
`Writes`, preservation of all registers except RDI/RSI/RSP/RIP, and preservation
of flags outside the arithmetic flag set. Its return-cell nonoverlap premise
establishes return to the original destination. The underlying `correct` theorem
also describes executions that overwrite the return cell: RET reads the updated
memory. Keeping these two statements separate makes the caller's obligation clear.

These are contracts for the total byte-array model. Mapped writable memory,
executable code integrity, and native resource limits remain caller/environment
obligations; enormous counts are mathematical termination results, not practical
native executions.

## Stack spill and temporary reservation

`stack32` reserves 32 bytes, stores RDI in the first eight, restores RSP, and
returns. `stack_correct` describes those exact eight bytes as the memory footprint,
preserves every register except RSP/RIP, and proves the original return destination
under a byte-disjointness premise. The newer `Callers.stack` wrapper proves that
premise once for all addresses; callers need no disjointness argument. Reserving
scratch does not imply that every reserved byte changes.

`reserve256` is a deliberately contrasting fixture. `reserve_completion` proves
its exit frame and return contract, yet `reserve_depth` proves that entry RSP
`0x8000` becomes `0x7f00` after the first instruction. An exit frame cannot certify
a 32-byte maximum stack depth.

[`StackBounds.stack32`](../Examples/StackBounds.lean) now proves the bound at every
instruction boundary for every entry state with `32 ≤ entryRSP.toNat`. `StackWithin`
uses natural addresses, so subtraction wraparound is rejected. The separate return
observation permits the required eight-byte RSP adjustment by RET.
`reserve256_exceeds32` proves failure of the same 32-byte bound for every entry
RSP at least 256. `Callers.stack_safe` packages the bound and existing memory/register
contract together. These observations do not assert access permissions or mapped
memory, and they do not replace the separate termination proof.

## Endpoint helpers for callers

[`Regions.lean`](../PcodeLean/Regions.lean) supplies `NoWrap base bytes` and
`Separated a n b m`. They use natural-number endpoints, accept adjacent buffers
and empty ranges, and reject address wraparound. An endpoint equal to 2⁶⁴ is valid
for a half-open range. They are sufficient conditions for ordinary buffers;
the original modular contracts remain available.

`Separated.read_write` converts these endpoint facts into the bytewise premise of
`readLE_frame`. Slice lemmas let a caller describe one 16-byte buffer rather than
each limb separately. `stack_scratch_separated` derives scratch/return separation
from the reservation size, a nonwrapping return cell, and absence of underflow.

[`Callers.add`](../Examples/Callers.lean) accepts each input either at exactly the
output address or in a separate 16-byte buffer, plus separation from the return
cell. It supports left in-place, right in-place, and fully separate output.
`Callers.fill` needs just the separation of its `8 * count` output bytes from the
return cell, including count zero. The checked examples in
[`CallerChecks.lean`](../Examples/CallerChecks.lean) use arbitrary memory and
concrete addresses; no byte-by-byte proof or unfolding of generated steps is needed.
They also check adjacency, empty output inside the return cell, the last valid
address, rejected overlap/wraparound, and stack subtraction underflow.

The small [`Trace.lean`](../PcodeLean/Trace.lean) helper checks an invariant along
every finite execution prefix. `always_invariant` proves it from a single-step
rule; `Always.post` recovers the ordinary return contract. Zero fuel still checks
the initial state, and a finite observation never asserts termination.

## Reliability checks

The normal integration test regenerates all four models from the assembly,
rebuilds their proofs, and audits theorem axioms. Native checks compare complete
96-byte buffers and addition carries with both Lean execution and a separate
Python byte reference. The 51 cases cover zero counts, surrounding bytes, exact
input/output aliases, carry propagation, overflow, and partial overlaps. Unsafe
partial overlaps test the actual instruction sequence; they do not strengthen
the aliasing theorem's hypotheses. Five additional native/model checks read back
the stack-spill value after return.

The proofs establish properties of the generated model. Native comparisons can
find translation errors but do not certify SLEIGH's ISA semantics. The existing
auxiliary-carry discrepancy remains an explicit regression.
