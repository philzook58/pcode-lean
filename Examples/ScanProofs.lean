import Examples.Generated.Scan

open PcodeLean Std.WP Lean.Order
set_option experimental.vcgen true

namespace Examples.ScanProof

/-- OR of the little-endian limbs, allowing modular addresses in the flat memory model. -/
def limbOr (mem : Memory) (base : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => readLE mem base 8 ||| limbOr mem (base + 8) n

private def invariant (s : X86State) (f : Scan.Frame) : Prop :=
  f.2.mem = s.mem ∧ f.2.rsp = s.rsp ∧
  match f.1 with
  | .p0 => f.2.rdi = s.rdi ∧ f.2.rsi = s.rsi
  | .p1 => f.2.rax = 0 ∧ f.2.rdi = s.rdi ∧ f.2.rsi = s.rsi
  | .p2 | .p6 =>
    f.2.rax ||| limbOr s.mem f.2.rsi f.2.rdi.toNat = limbOr s.mem s.rsi s.rdi.toNat ∧
    f.2.zf = boolByte (f.2.rdi == 0)
  | .p3 =>
    f.2.rax ||| limbOr s.mem f.2.rsi f.2.rdi.toNat = limbOr s.mem s.rsi s.rdi.toNat ∧
    f.2.rdi ≠ 0
  | .p4 =>
    f.2.rax ||| limbOr s.mem (f.2.rsi + 8) (f.2.rdi.toNat - 1) =
      limbOr s.mem s.rsi s.rdi.toNat ∧ f.2.rdi ≠ 0
  | .p5 =>
    f.2.rax ||| limbOr s.mem f.2.rsi (f.2.rdi.toNat - 1) =
      limbOr s.mem s.rsi s.rdi.toNat ∧ f.2.rdi ≠ 0
  | .p7 => f.2.rax = limbOr s.mem s.rsi s.rdi.toNat

private theorem sub_one (x : BitVec 64) (h : x ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have hpos := BitVec.toNat_pos_of_ne_zero h
  have hx : (1 : BitVec 64) ≤ x := by change 1 ≤ x.toNat; omega
  simpa using BitVec.toNat_sub_of_le hx

def Post (s out : X86State) : Prop :=
  out.rax = limbOr s.mem s.rsi s.rdi.toNat ∧ StackReturn s out ∧ out.mem = s.mem

private theorem block (s : X86State) (f : Scan.Frame) :
    ⦃invariant s f⦄ Scan.step f ⦃Sum.elim (invariant s) (Post s)⦄ := by
  rcases f with ⟨pc, state⟩
  cases pc <;> vcgen [Scan.step]
  all_goals simp_all [invariant, Post, StackReturn, Sum.elim, boolByte, limbOr]
  all_goals rename_i hpre
  all_goals rcases hpre with ⟨hm, hsp, heq, hne⟩
  all_goals first
    | (change state.rax ||| limbOr s.mem state.rsi (state.rdi - 1).toNat =
         limbOr s.mem s.rsi s.rdi.toNat
       rw [sub_one state.rdi hne]; exact heq)
    | (have hp := BitVec.toNat_pos_of_ne_zero hne
       have hn : state.rdi.toNat = (state.rdi.toNat - 1) + 1 := by omega
       have hs : limbOr s.mem state.rsi state.rdi.toNat =
           readLE s.mem state.rsi 8 ||| limbOr s.mem (state.rsi + 8)
             (state.rdi.toNat - 1) := by
         conv => lhs; rw [hn]
         rfl
       rw [hs, ← BitVec.or_assoc] at heq
       exact heq)

theorem correct (s : X86State) : ⦃True⦄ Scan.run s ⦃Post s⦄ := by
  constructor
  intro _
  exact (run_spec Scan.step (Scan.initial s) (invariant s) (Post s) (block s)).le_wp
    (by simp [invariant, Scan.initial])

private def rank (f : Scan.Frame) : Nat :=
  match f.1 with
  | .p0 => 4 * f.2.rdi.toNat + 4
  | .p1 => 4 * f.2.rdi.toNat + 3
  | .p2 | .p6 => 4 * f.2.rdi.toNat + 2
  | .p3 => 4 * f.2.rdi.toNat + 1
  | .p4 => 4 * f.2.rdi.toNat
  | .p5 => 4 * f.2.rdi.toNat - 1
  | .p7 => 0

private theorem decreases (s : X86State) (f : Scan.Frame) (hi : invariant s f) :
    Sum.elim (fun f' ↦ invariant s f' ∧ rank f' < rank f) (Post s) (Scan.step f) := by
  have hc := (block s f).le_wp hi
  change Sum.elim (invariant s) (Post s) (Scan.step f) at hc
  rcases f with ⟨pc, state⟩
  cases pc <;> simp only [Scan.step, invariant, rank, Sum.elim, boolByte, pure] at *
  all_goals rcases hi with ⟨hm, hsp, hvalue⟩
  all_goals try rcases hvalue with ⟨heq, hne⟩
  all_goals simp_all
  all_goals try (split <;> simp_all)
  all_goals have hne' : state.rdi ≠ 0 := by first | exact hne | exact hc.2
  all_goals have hpos := BitVec.toNat_pos_of_ne_zero hne'
  all_goals first
    | omega
    | (change 4 * (state.rdi - (1 : BitVec 64)).toNat + 2 < 4 * state.rdi.toNat - 1
       rw [sub_one state.rdi hne']; omega)

theorem terminates (s : X86State) :
    ∃ out, Scan.execute (4 * s.rdi.toNat + 5) s = some out ∧ Post s out := by
  apply finishes_execute Scan.step (Scan.initial s)
  exact finishes_of_rank Scan.step (invariant s) rank (Post s) (decreases s)
    (Scan.initial s) (by simp [invariant, Scan.initial])

end Examples.ScanProof
