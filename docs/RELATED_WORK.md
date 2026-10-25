# Assembly verification precedents

Sources inspected on 2026-10-23. These are design references, not dependencies,
imported proofs, or certificates for this exporter. Recommendations below are
our interpretation of the sources.

## s2n-bignum: contracts and proof structure

s2n-bignum uses **HOL Light**, distinct from HOL4. Its
[word_max proof](https://github.com/awslabs/s2n-bignum/blob/main/x86/proofs/word_max.ml)
checks a literal byte sequence against an object file, derives an execution rule,
and proves a mathematical result together with an explicit `MAYCHANGE` relation.
It separates the core computation from return/ABI wrappers. In the inspected
proof, removing the leading `ENDBR64` gives exactly our existing maximum fixture:

```text
48 89 f8 48 39 f7 48 0f 42 c6 c3
```

This establishes a useful benchmark correspondence. Our current proof remains
about our p-code model; matching bytes does not import the HOL Light theorem or
establish equivalence between the two instruction models.

The [bignum_nonzero proof](https://github.com/awslabs/s2n-bignum/blob/main/x86/proofs/bignum_nonzero.ml)
is a useful next example: its loop relates a memory representation of an integer,
the remaining limb count, the accumulated OR, and the zero flag. Its mathematical
contract is followed by separate subroutine wrappers.

Lessons for this project:

* Strengthen contracts with a small register-clobber predicate, including
  preservation of callee-saved registers. The current `Returns` predicate covers
  the result, stack, return address, and data memory, but not that register frame.
* Keep core correctness, termination, and ABI obligations separate and reusable.
* Preserve exact-byte regeneration checks. When ELF input is introduced, bind
  proofs to the selected object bytes and address assumptions explicitly.
* Start memory proofs with a read-only limb scan before general bignum addition.
  Introduce only the memory/word lemmas that example needs.

The sibling ASMC project already vendors `word_max.S`, `bignum_add.S`, headers,
and license material at revision `4d1356a7470663c752660a59375dc3a9ef548428`.
Use that provenance if importing those fixtures; the current prototype's examples
were written locally. Check revision and license separately for any new import.

## HOL4: certify the extracted model

Myreen, Gordon, and Slind's
[decompilation into logic](https://www.cl.cam.ac.uk/~mom22/decompilation/)
extracts logical functions from machine code and produces a correctness theorem
relative to an ISA model. The generated function is a tractable proof target,
with a certificate connecting it back to machine execution.

[HolBA](https://github.com/kth-step/HolBA) similarly provides proof-producing
lifting to BIR and transfer of BIR contracts back to ISA contracts. Its documented
targets include ARMv8, Cortex-M0, and RISC-V; it is not an existing x86 proof
backend for this prototype.

Our direct, shallow Lean output fits the extracted-function approach in spirit,
but currently has no lifting certificate. There are two distinct future claims:

1. Generated Lean implements the relevant raw p-code semantics.
2. Those p-code semantics correctly model the selected ISA instructions.

Proving the first would reduce trust in the C++ printer, while leaving SLEIGH's
instruction definitions trusted. Proving both needs an independent ISA reference
and an explicit state relation. Neither alone proves correspondence to physical
hardware. Keep this work scoped to a small instruction subset; do not build a
general certifying decompiler before an example justifies it.

## Isabelle: abstraction and instruction summaries

The AFP entry
[X86 instruction semantics and basic block symbolic execution](https://www.isa-afp.org/entries/X86_Semantics.html)
models register aliases and byte memory. Its `se_step` method uses memory lemmas
to simplify symbolic execution. Missing or deliberately unspecified semantics
are parameterized by universally quantified uninterpreted terms.

The useful principle is to make imprecision explicit. In particular, an omitted
architectural flag update must not acquire a native-correctness claim merely
because raw p-code leaves the flag cell unchanged. Our observed AF discrepancy
is a defined architectural effect missing from the lift, not just an undefined
flag. A future architectural abstraction could conservatively forget such
effects, with a separate justification; preserve the raw export's meaning.

[IsaBIL](https://arxiv.org/html/2504.16775v1) formalizes BAP's BIL in Isabelle and
develops larger proof rules, including instruction-level RISC-V rules, to reduce
repeated low-level reasoning. Its discussion of verified lifting explicitly
distinguishes IR verification from proving correctness of the assembly lift.

For us, derive reusable instruction/block summaries from generated Lean when
manual proofs start repeating. Keep `vcgen` as the proof interface and avoid
adding a separate symbolic-execution engine just to obtain these summaries.

## Proposed next small steps

1. Add explicit register preservation to the current contracts.
2. Prove one read-only limb scan with a mathematical memory-view specification.
3. Prove a two-limb add-with-carry before tackling a variable-length adder.
4. Reuse a mathematical specification for a small C/assembly/RTL comparison;
   state ABI, source-language, and hardware observation assumptions separately.
5. Add instruction-refinement certificates only for the subset actually needed.

The first three steps are now implemented: explicit frames, a read-only OR scan,
and a two-limb register adder with a carry theorem. See the
[checked tutorial](TUTORIAL.md). [Memory-output addition, fill, and a stack spill](WRITES.md)
are also implemented, with buffer endpoint helpers and instruction-boundary stack
bounds. Cross-tool correspondence and lift certification remain follow-ups.
No HOL/Isabelle runtime, proof importer, or universal IR was added.
