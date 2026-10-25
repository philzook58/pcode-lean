import Examples.WriteProofs
import PcodeLean.Trace

open PcodeLean
namespace Examples.StackBounds

private def position (entry : BitVec 64) (f : Stack32.Frame) : Prop :=
  f.2.rsp = match f.1 with
    | .p1 | .p2 => entry - 32
    | .p0 | .p3 => entry

private theorem movement (s : X86State) :
    Always Stack32.step (Stack32.initial s) (position s.rsp)
      (fun out ↦ out.rsp = s.rsp + 8) := by
  apply always_invariant _ _ (by rfl)
  intro ⟨pc, state⟩ h
  cases pc <;> simp only [position] at h
  all_goals simp [Stack32.step, position, pure, Sum.elim, h, BitVec.sub_add_cancel]

/-- All instruction boundaries stay within 32 bytes below entry; RET advances RSP by eight. -/
theorem stack32 (s : X86State) (hs : 32 ≤ s.rsp.toNat) :
    Always Stack32.step (Stack32.initial s)
      (fun f ↦ StackWithin s.rsp 32 f.2.rsp) (fun out ↦ out.rsp = s.rsp + 8) := by
  apply (movement s).mono ?_ (fun _ h ↦ h)
  intro ⟨pc, state⟩ h
  have ht : (s.rsp - 32).toNat = s.rsp.toNat - 32 :=
    BitVec.toNat_sub_of_le (by change 32 ≤ s.rsp.toNat; exact hs)
  cases pc <;> simp only [position] at h
  all_goals simp only [StackWithin, h, ht]; omega

/-- An actual 256-byte reservation violates a 32-byte bound immediately, despite its exit frame. -/
theorem reserve256_exceeds32 (s : X86State) (hs : 256 ≤ s.rsp.toNat) :
    ¬Always Reserve256.step (Reserve256.initial s)
      (fun f ↦ StackWithin s.rsp 32 f.2.rsp) (fun out ↦ out.rsp = s.rsp + 8) := by
  intro h
  have first := (h 1).2
  change StackWithin s.rsp 32 (s.rsp - 256) at first
  have ht : (s.rsp - 256).toNat = s.rsp.toNat - 256 :=
    BitVec.toNat_sub_of_le (by change 256 ≤ s.rsp.toNat; exact hs)
  simp only [StackWithin, ht] at first
  omega

end Examples.StackBounds
