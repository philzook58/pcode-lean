import Examples.Generated.Fill
import PcodeLean.Frame
open PcodeLean
namespace Examples.FillProof

def fillMemory (mem : Memory) (base : BitVec 64) (v : BitVec 64) : Nat → Memory
  | 0 => mem
  | n + 1 => fillMemory (writeLE mem base 8 v) (base + 8) v n

/-- Exact union of stores, including modular address wraparound. -/
def Writes (base : BitVec 64) : Nat → BitVec 64 → Prop
  | 0, _ => False
  | n + 1, p => ByteRegion base 8 p ∨ Writes (base + 8) n p

def registerFrame : Footprint :=
  ⟨[.rdi, .rsi, .rsp, .rip], arithmeticFlags, fun _ ↦ True⟩

def footprint (s : X86State) : Footprint :=
  { registerFrame with memory := Writes s.rdi s.rsi.toNat }

def Post (s out : X86State) (n : Nat) : Prop :=
  out.mem = fillMemory s.mem s.rdi s.rdx n ∧ out.rsp = s.rsp + 8 ∧
    out.rip = readLE (fillMemory s.mem s.rdi s.rdx n) s.rsp 8 ∧
    MayChange registerFrame s out

set_option maxRecDepth 4096 in
private theorem loop (n : Nat) (s : X86State) (hc : s.rsi.toNat = n)
    (hz : s.zf = boolByte (s.rsi == 0)) :
    finishes Fill.step (4*n+2) (.p5, s) (Post s · n) := by
  induction n generalizing s with
  | zero =>
    have he : s.rsi = 0 := BitVec.eq_of_toNat_eq hc
    simp [finishes, Fill.step, Post, fillMemory, hz, he, boolByte, pure, Sum.elim, MayChange, registerFrame,
      Register.forall_iff, Flag.forall_iff,
      Register.read, Flag.read, arithmeticFlags]
  | succ n ih =>
    have hn : s.rsi ≠ 0 := by intro h; simp [h] at hc
    have hzf : s.zf = 0 := by
      rw [hz]
      simp only [boolByte, beq_iff_eq, ite_eq_right_iff]
      intro h
      exact False.elim (hn h)
    have hle : (1 : BitVec 64) ≤ s.rsi := by change 1 ≤ s.rsi.toNat; omega
    have hsub : (s.rsi - 1).toNat = n := by rw [BitVec.toNat_sub_of_le hle]; simp [hc]
    let next : X86State := { s with
      rip := 0x100f
      mem := writeLE s.mem s.rdi 8 s.rdx
      rdi := s.rdi + 8
      rsi := s.rsi - 1
      zf := boolByte (s.rsi - 1 == 0)
      sf := boolByte ((s.rsi - 1).slt 0)
      of := boolByte ((s.rsi.msb != (1 : BitVec 64).msb) &&
        ((s.rsi - 1).msb != s.rsi.msb))
      pf := boolByte ((BitVec.ofNat 8 (popcount ((s.rsi - 1) &&& 255)) &&& 1) == 0) }
    have hnext := ih next (by exact hsub) rfl
    have he : 4*(n+1)+2 = (4*n+2)+4 := by omega
    rw [he]
    by_cases hznext : s.rsi - 1 = 0
    all_goals simpa [finishes, Fill.step, Post, fillMemory, next, hzf, hznext,
      boolByte, pure, Sum.elim, MayChange, registerFrame,
      Register.forall_iff, Flag.forall_iff,
      Register.read, Flag.read, arithmeticFlags] using hnext

theorem completion (s : X86State) :
    finishes Fill.step (4*s.rsi.toNat+3) (Fill.initial s) (Post s · s.rsi.toNat) := by
  let start : X86State := { s with
    cf := 0, of := 0, sf := boolByte (s.rsi.slt 0), zf := boolByte (s.rsi == 0),
    pf := boolByte ((BitVec.ofNat 8 (popcount (s.rsi &&& 255)) &&& 1) == 0), rip := 0x1003 }
  have h := loop s.rsi.toNat start rfl rfl
  have he : 4*s.rsi.toNat+3 = (4*s.rsi.toNat+2)+1 := by omega
  rw [he]
  simpa [finishes, Fill.step, Fill.initial, Post, start, boolByte, pure, Sum.elim, MayChange, registerFrame,
      Register.forall_iff, Flag.forall_iff,
      Register.read, Flag.read, arithmeticFlags] using h

/-- No byte outside the union of stores is changed. -/
theorem memory_frame (mem : Memory) (base v : BitVec 64) (n : Nat) :
    ∀ p, ¬Writes base n p → fillMemory mem base v n p = mem p := by
  induction n generalizing mem base with
  | zero => intro p hp; rfl
  | succ n ih =>
    intro p hp
    have hfirst : ¬ByteRegion base 8 p := fun h ↦ hp (Or.inl h)
    have hrest : ¬Writes (base + 8) n p := fun h ↦ hp (Or.inr h)
    exact (ih _ _ p hrest).trans (writeLE_outside _ _ _ _ _ hfirst)

theorem correct (s : X86State) : (Fill.run s).wp (Post s · s.rsi.toNat) :=
  finishes_run _ _ _ (completion s)

theorem terminates (s : X86State) :
    ∃ out, execute Fill.step (4*s.rsi.toNat+3) (Fill.initial s) = some out ∧
      Post s out s.rsi.toNat := finishes_execute _ _ _ (completion s)

/-- A caller protects its return cell by keeping the output footprint disjoint. -/
theorem caller_contract (s : X86State)
    (hr : ∀ p, ReadRegion s.rsp 8 p → ¬Writes s.rdi s.rsi.toNat p) :
    (Fill.run s).wp (fun out ↦ Post s out s.rsi.toNat ∧ StackReturn s out ∧
      MayChange (footprint s) s out) := by
  apply (Fill.run s).mono (fun out h ↦ ?_) (correct s)
  have hm : ∀ p, ¬Writes s.rdi s.rsi.toNat p → out.mem p = s.mem p := by
    intro p hp
    rw [h.1]
    exact memory_frame _ _ _ _ p hp
  refine ⟨h, ⟨h.2.1, ?_⟩, h.2.2.2.1, h.2.2.2.2.1, hm⟩
  exact h.2.2.1.trans (readLE_frame _ _ _ (memory_frame _ _ _ _) _ _ hr)

end Examples.FillProof
