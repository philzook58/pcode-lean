import Examples.Callers

open PcodeLean
namespace Examples.CallerChecks

-- Adjacent buffers and the final address are valid; one-byte overlap and wrap are rejected.
example : Separated 0x6000 16 0x6010 16 := by decide
example : ¬Separated 0x6000 16 0x600f 16 := by decide
example : NoWrap 0xffffffffffffffff 1 := by decide
example : ¬NoWrap 0xffffffffffffffff 2 := by decide
example : Separated 0x8000 8 0x8004 0 := by decide
example : Separated 0x8004 0 0x8000 8 := by decide

-- Real caller contracts with arbitrary initial memory and unspecified registers.
theorem inplace_left (s : X86State) :
    let input := { s with rdi := 0x6000, rsi := 0x6000, rdx := 0x6010, rsp := 0x8000 }
    (AddMem.run input).wp (WriteProof.AddPost input) :=
  Callers.add _ (Or.inl rfl) (Or.inr (by dsimp only; decide)) (by dsimp only; decide)

theorem inplace_right (s : X86State) :
    let input := { s with rdi := 0x6010, rsi := 0x6000, rdx := 0x6010, rsp := 0x8000 }
    (AddMem.run input).wp (WriteProof.AddPost input) :=
  Callers.add _ (Or.inr (by dsimp only; decide)) (Or.inl rfl) (by dsimp only; decide)

theorem separate_output (s : X86State) :
    let input := { s with rdi := 0x6020, rsi := 0x6000, rdx := 0x6010, rsp := 0x8000 }
    (AddMem.run input).wp (WriteProof.AddPost input) :=
  Callers.add _ (Or.inr (by dsimp only; decide)) (Or.inr (by dsimp only; decide))
    (by dsimp only; decide)

theorem empty_fill_at_return (s : X86State) :
    let input := { s with rdi := 0x8004, rsi := 0, rsp := 0x8000 }
    (Fill.run input).wp (fun out ↦ FillProof.Post input out 0 ∧ StackReturn input out ∧
      MayChange (FillProof.footprint input) input out) := Callers.fill _ (by dsimp only; decide)

theorem bounded_spill (s : X86State) :
    let input := { s with rsp := 0x8000 }
    Always Stack32.step (Stack32.initial input)
      (fun f ↦ StackWithin input.rsp 32 f.2.rsp) (fun out ↦ out.rsp = input.rsp + 8) ∧
      (Stack32.run input).wp (WriteProof.StackPost input) :=
  Callers.stack_safe _ (by dsimp only; decide)

-- The universal depth theorem includes the smallest non-underflowing entry stack pointer.
example : Always Stack32.step (Stack32.initial { rsp := 32 })
    (fun f ↦ StackWithin 32 32 f.2.rsp) (fun out ↦ out.rsp = 40) :=
  StackBounds.stack32 _ (by dsimp only; decide)

-- A frame bound must reject subtraction wraparound, including when the exit restores RSP.
example : ¬Always Stack32.step (Stack32.initial { rsp := 31 })
    (fun f ↦ StackWithin 31 32 f.2.rsp) (fun out ↦ out.rsp = 39) := by
  intro h
  have first := (h 1).2
  change StackWithin 31 32 (31 - 32) at first
  revert first
  decide

end Examples.CallerChecks
