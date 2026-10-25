# Dependencies and references

* [Trail of Bits / lifting-bits SLEIGH](https://github.com/lifting-bits/sleigh),
  revision `feddce193fe480ce868d7ddd38ce03f38d60ac50`: standalone CMake packaging
  and C++ API. Its upstream license and notices remain in fetched source.
* [NSA Ghidra](https://github.com/NationalSecurityAgency/ghidra),
  `Ghidra_12.1.4_build` with SLEIGH's stable patches: decoder and x86 language
  specifications. Its license and dependency notices remain in fetched source.
* [Lean 4 / Std](https://github.com/leanprover/lean4), version 4.35.0:
  bitvectors, the weakest-precondition framework, `vcgen`, and checked bitvector
  automation. Their licenses remain in the Lean distribution.

The frontend follows the documented `LoadImage`, `PcodeEmit`, `AssemblyEmit`, and
`Sleigh.oneInstruction` APIs. The local ASMC project informed the initialization
sequence and the explicit auxiliary-carry regression; it is not linked or vendored.
The local goto-lean project informed the small finite-prefix/invariant proof interface.
All assembly examples and native harnesses in this project are written locally.
The memory-output adder, fill loop, and stack fixtures were informed by the sibling
ASMC `tests/challenges.S` and `examples/stack/frames.S`, and the sibling goto-lean
loop examples; no upstream assembly or proof files were imported.
The frame contracts and new walkthrough were informed by s2n-bignum's
[x86 tutorials](https://github.com/awslabs/s2n-bignum/tree/main/x86/tutorial),
particularly `memory.ml` and `bignum.ml`, inspected on 2026-10-23. Their code and
HOL Light proofs were not copied or imported.

Semantic references supplied for the design:

* [Ghidra p-code manual, 11.3.1](https://github.com/NationalSecurityAgency/ghidra/blob/Ghidra_11.3.1_build/GhidraDocs/languages/html/pcoderef.html)
  and [SLEIGH manual, 11.3.1](https://github.com/NationalSecurityAgency/ghidra/blob/Ghidra_11.3.1_build/GhidraDocs/languages/html/sleigh.html).
  These are conceptual references, not the version pin used to generate models.
* [Ghidra emulate.cc](https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/emulate.cc)
  and [opbehavior.cc](https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/opbehavior.cc).
* [Knuckledragger p-code model](https://github.com/philzook58/knuckledragger/blob/176d9840f744ad8812a481b34c85e93f75070a4b/src/kdrag/contrib/pcode/__init__.py),
  read as a design reference; no Python interpreter or binding is imported.
