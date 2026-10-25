import Examples.WriteProofs
import Examples.FillProofs
import Examples.StackBounds
import PcodeLean.Regions

open PcodeLean
namespace Examples.Callers

private theorem high_stable (out input : BitVec 64)
    (h : out = input ∨ Separated out 16 input 16) :
    ∀ p, ReadRegion (input + 8) 8 p → ¬ByteRegion out 8 p := by
  intro p hp hw
  rcases h with rfl | h
  · exact ReadRegion.high_limb _ _ hp hw
  · have hi := ReadRegion.slice h.2.1 (off := 8) (by decide) hp
    have ho := ByteRegion.slice h.1 (off := 0) (bytes := 8) (by decide) (by simpa using hw)
    exact h.byte_disjoint p ho hi

/-- Each input may alias the output exactly or occupy a separate 16-byte buffer. -/
theorem add (s : X86State)
    (left : s.rdi = s.rsi ∨ Separated s.rdi 16 s.rsi 16)
    (right : s.rdi = s.rdx ∨ Separated s.rdi 16 s.rdx 16)
    (stack : Separated s.rsp 8 s.rdi 16) : (AddMem.run s).wp (WriteProof.AddPost s) := by
  apply WriteProof.add_correct s ⟨high_stable _ _ left, high_stable _ _ right⟩
  intro p hp
  constructor
  · intro hw
    exact stack.read_write p hp (ByteRegion.slice stack.2.1 (off := 0) (bytes := 8)
      (by decide) (by simpa using hw))
  · intro hw
    exact stack.read_write p hp (ByteRegion.slice stack.2.1 (off := 8) (by decide) hw)

/-- The recursive store footprint is contained in the caller's nonwrapping output buffer. -/
theorem fill_writes (hw : NoWrap base (8*n)) (hp : FillProof.Writes base n p) :
    ByteRegion base (8*n) p := by
  induction n generalizing base with
  | zero => exact False.elim hp
  | succ n ih =>
    rcases hp with hp | hp
    · exact ByteRegion.slice hw (off := 0) (bytes := 8) (by omega) (by simpa using hp)
    · by_cases hn : n = 0
      · subst n; exact False.elim hp
      · have hw' := (hw.offset (off := 8) (bytes := 8*n) (by omega) (by omega)).2
        exact ByteRegion.slice hw (off := 8) (by omega) (ih hw' hp)

/-- Fill callers supply two ranges rather than reasoning about each individual store. -/
theorem fill (s : X86State) (stack : Separated s.rsp 8 s.rdi (8*s.rsi.toNat)) :
    (Fill.run s).wp (fun out ↦ FillProof.Post s out s.rsi.toNat ∧ StackReturn s out ∧
      MayChange (FillProof.footprint s) s out) := by
  apply FillProof.caller_contract s
  intro p hp hw
  exact stack.read_write p hp (fill_writes stack.2.1 hw)

/-- This fixed-size spill cannot overlap its return cell, even with modular addresses. -/
theorem stack (s : X86State) : (Stack32.run s).wp (WriteProof.StackPost s) := by
  apply WriteProof.stack_correct s
  intro p hp
  simp only [ReadRegion, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h
  all_goals subst p; unfold ByteRegion; bv_omega

/-- Combine the memory/register contract with the bound checked throughout execution. -/
theorem stack_safe (s : X86State) (hs : 32 ≤ s.rsp.toNat) :
    Always Stack32.step (Stack32.initial s)
      (fun f ↦ StackWithin s.rsp 32 f.2.rsp) (fun out ↦ out.rsp = s.rsp + 8) ∧
      (Stack32.run s).wp (WriteProof.StackPost s) := ⟨StackBounds.stack32 s hs, stack s⟩

end Examples.Callers
