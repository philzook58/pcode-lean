import Examples.Generated.Increment
import Examples.Generated.Maximum
import Examples.Generated.Count

/-! Proofs are independent of the generator. These contracts concern the emitted p-code model.
They do not certify SLEIGH's correspondence to the processor. -/
open PcodeLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace Examples

/-- Result, stack adjustment, return destination, and preservation of data memory. -/
def Returns (before after : X86State) (result : BitVec 64) : Prop :=
  after.rax = result ∧ after.rsp = before.rsp + 8 ∧
    after.rip = readLE before.mem before.rsp 8 ∧ after.mem = before.mem

private def frame (before after : X86State) : Prop :=
  after.rsp = before.rsp ∧ after.mem = before.mem

namespace IncrementProof

private def invariant (s : X86State) (f : Increment.Frame) : Prop :=
  frame s f.2 ∧ match f.1 with
    | .p0 => f.2.rdi = s.rdi
    | .p1 => f.2.rax = s.rdi + 1

private theorem block (s : X86State) (f : Increment.Frame) :
    ⦃invariant s f⦄ Increment.step f ⦃Sum.elim (invariant s) (Returns s · (s.rdi + 1))⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc <;> vcgen [Increment.step]
  all_goals simp_all [invariant, frame, Returns, Sum.elim]

theorem correct (s : X86State) :
    ⦃True⦄ Increment.run s ⦃fun out ↦ Returns s out (s.rdi + 1)⦄ := by
  constructor
  intro _
  exact (run_spec Increment.step (Increment.initial s) (invariant s) _ (block s)).le_wp
    (by simp [invariant, frame, Increment.initial])

theorem terminates (s : X86State) :
    ∃ out, Increment.execute 2 s = some out ∧ Returns s out (s.rdi + 1) := by
  apply finishes_execute Increment.step (Increment.initial s)
  simp [finishes, Increment.step, Increment.initial, Returns, Sum.elim, pure]

end IncrementProof

namespace MaximumProof

def result (s : X86State) : BitVec 64 := if s.rdi.ult s.rsi then s.rsi else s.rdi

private def invariant (s : X86State) (f : Maximum.Frame) : Prop :=
  frame s f.2 ∧ f.2.rdi = s.rdi ∧ f.2.rsi = s.rsi ∧ match f.1 with
    | .p0 => True
    | .p1 => f.2.rax = s.rdi
    | .p2 => f.2.rax = s.rdi ∧ f.2.cf = boolByte (s.rdi.ult s.rsi)
    | .p3 => f.2.rax = result s

private theorem block (s : X86State) (f : Maximum.Frame) :
    ⦃invariant s f⦄ Maximum.step f ⦃Sum.elim (invariant s) (Returns s · (result s))⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc <;> vcgen [Maximum.step]
  all_goals simp_all [invariant, frame, Returns, Sum.elim, result, boolByte]
  all_goals split <;> simp_all

theorem correct (s : X86State) :
    ⦃True⦄ Maximum.run s ⦃fun out ↦ Returns s out (result s)⦄ := by
  constructor
  intro _
  exact (run_spec Maximum.step (Maximum.initial s) (invariant s) _ (block s)).le_wp
    (by simp [invariant, frame, Maximum.initial])

theorem terminates (s : X86State) :
    ∃ out, Maximum.execute 4 s = some out ∧ Returns s out (result s) := by
  apply finishes_execute Maximum.step (Maximum.initial s)
  simp [finishes, Maximum.step, Maximum.initial, Returns, Sum.elim, result, boolByte, pure]
  split <;> simp_all

end MaximumProof

namespace CountProof

private theorem clear_low32 (x : BitVec 64) :
    (BitVec.extractLsb' 0 32 (x &&& 0xffffffff00000000)).setWidth 64 = 0 := by
  rw [BitVec.extractLsb'_and]
  change ((BitVec.extractLsb' 0 32 x &&& (0 : BitVec 32)).setWidth 64) = 0
  simp

private theorem inc_sum (a b n : BitVec 64) (h : a + b = n) : a + 1 + b = n + 1 := by
  rw [BitVec.add_assoc, BitVec.add_comm (1 : BitVec 64) b, ← BitVec.add_assoc, h]

private theorem dec_sum (a b n : BitVec 64) (h : a + b = n + 1) : a + (b - 1) = n := by
  calc
    a + (b - 1) = (a + b) - 1 := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    _ = (n + 1) - 1 := congrArg (· - 1) h
    _ = n := BitVec.add_sub_cancel n 1

private def invariant (s : X86State) (f : Count.Frame) : Prop :=
  frame s f.2 ∧ match f.1 with
    | .p0 => f.2.rdi = s.rdi
    | .p1 => f.2.rax = 0 ∧ f.2.rdi = s.rdi
    | .p2 | .p5 => f.2.rax + f.2.rdi = s.rdi ∧ f.2.zf = boolByte (f.2.rdi == 0)
    | .p3 => f.2.rax + f.2.rdi = s.rdi ∧ f.2.rdi ≠ 0
    | .p4 => f.2.rax + f.2.rdi = s.rdi + 1 ∧ f.2.rdi ≠ 0
    | .p6 => f.2.rax = s.rdi

private theorem block (s : X86State) (f : Count.Frame) :
    ⦃invariant s f⦄ Count.step f ⦃Sum.elim (invariant s) (Returns s · s.rdi)⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc <;> vcgen [Count.step]
  all_goals simp_all [invariant, frame, Returns, Sum.elim, boolByte]
  all_goals try simp_all [insertBits]
  all_goals rename_i hpre
  all_goals rcases hpre with ⟨hframe, hvalue⟩
  all_goals try rcases hvalue with ⟨heq, hne⟩
  all_goals first
    | exact clear_low32 _
    | exact inc_sum _ _ _ heq
    | exact dec_sum _ _ _ heq

/-- The loop returns its original input for every 64-bit count, without an unwinding bound. -/
theorem correct (s : X86State) : ⦃True⦄ Count.run s ⦃fun out ↦ Returns s out s.rdi⦄ := by
  constructor
  intro _
  exact (run_spec Count.step (Count.initial s) (invariant s) _ (block s)).le_wp
    (by simp [invariant, frame, Count.initial])

private def rank (f : Count.Frame) : Nat :=
  match f.1 with
  | .p0 => 3 * f.2.rdi.toNat + 4
  | .p1 => 3 * f.2.rdi.toNat + 3
  | .p2 | .p5 => 3 * f.2.rdi.toNat + 2
  | .p3 => 3 * f.2.rdi.toNat + 1
  | .p4 => 3 * f.2.rdi.toNat
  | .p6 => 0

private theorem sub_one (x : BitVec 64) (h : x ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have hpos := BitVec.toNat_pos_of_ne_zero h
  have hx : (1 : BitVec 64) ≤ x := by change 1 ≤ x.toNat; omega
  simpa using BitVec.toNat_sub_of_le hx

private theorem decreases (s : X86State) (f : Count.Frame) (hi : invariant s f) :
    Sum.elim (fun f' ↦ invariant s f' ∧ rank f' < rank f) (Returns s · s.rdi)
      (Count.step f) := by
  have hc := (block s f).le_wp hi
  change Sum.elim (invariant s) (Returns s · s.rdi) (Count.step f) at hc
  rcases f with ⟨pc, state⟩
  cases pc <;> simp only [Count.step, invariant, rank, frame, Sum.elim, boolByte, pure] at *
  all_goals rcases hi with ⟨hframe, hvalue⟩
  all_goals try rcases hvalue with ⟨heq, hne⟩
  all_goals simp_all
  all_goals try (split <;> simp_all)
  change 3 * (state.rdi - (1 : BitVec 64)).toNat + 2 < 3 * state.rdi.toNat
  rw [sub_one state.rdi hne]
  have hpos := BitVec.toNat_pos_of_ne_zero hne
  omega

/-- A rank proves completion even when concrete execution of the count would be impractical. -/
theorem terminates (s : X86State) :
    ∃ out, Count.execute (3 * s.rdi.toNat + 5) s = some out ∧ Returns s out s.rdi := by
  apply finishes_execute Count.step (Count.initial s)
  exact finishes_of_rank Count.step (invariant s) rank (Returns s · s.rdi) (decreases s)
    (Count.initial s) (by simp [invariant, frame, Count.initial])

end CountProof

#print axioms IncrementProof.correct
#print axioms MaximumProof.correct
#print axioms CountProof.correct
#print axioms CountProof.terminates

end Examples
