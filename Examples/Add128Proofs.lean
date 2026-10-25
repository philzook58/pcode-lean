import Examples.Generated.Add128

open PcodeLean Std.WP Lean.Order
namespace Examples.Add128Proof

def carry (x y : BitVec 64) : BitVec 8 := boolByte ((x + y).ult x)
def low (s : X86State) := s.rdi + s.rdx
def high (s : X86State) := s.rsi + s.rcx + (carry s.rdi s.rdx).setWidth 64
def overflow (s : X86State) := boolByte
  ((carry s.rsi s.rcx != 0) || (carry (s.rsi + s.rcx) ((carry s.rdi s.rdx).setWidth 64) != 0))

private theorem carry_add (x y : BitVec 64) :
    (x + y).toNat + 2^64 * (carry x y).toNat = x.toNat + y.toNat := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [carry, boolByte, BitVec.ult, BitVec.toNat_add]
  split <;> simp_all <;> omega

set_option maxRecDepth 2048 in
/-- Exact natural-number addition, including the 129th carry bit. -/
theorem arithmetic (s : X86State) :
    (low s).toNat + 2^64 * (high s).toNat + 2^128 * (overflow s).toNat =
      (s.rdi.toNat + 2^64 * s.rsi.toNat) + (s.rdx.toNat + 2^64 * s.rcx.toNat) := by
  have h0 := carry_add s.rdi s.rdx
  have h1 := carry_add s.rsi s.rcx
  have h2 := carry_add (s.rsi + s.rcx) ((carry s.rdi s.rdx).setWidth 64)
  have hb := (s.rsi + s.rcx).isLt
  have hx := s.rsi.isLt
  have hy := s.rcx.isLt
  cases hc0 : (s.rdi + s.rdx).ult s.rdi <;>
    cases hc1 : (s.rsi + s.rcx).ult s.rsi <;>
    cases hc2 : ((s.rsi + s.rcx) + (carry s.rdi s.rdx).setWidth 64).ult
      (s.rsi + s.rcx)
  all_goals simp [carry, boolByte, hc0] at hc2
  all_goals simp [low, high, overflow, carry, boolByte, hc0, hc1, hc2] at h0 h1 h2 ⊢
  all_goals omega

def Post (s out : X86State) : Prop :=
  out.rax = low s ∧ out.rdx = high s ∧ out.cf = overflow s ∧
    StackReturn s out ∧ out.mem = s.mem

private theorem completion (s : X86State) :
    finishes Add128.step 5 (Add128.initial s) (Post s) := by
  simp [finishes, Add128.step, Add128.initial, Post, StackReturn, low, high,
    overflow, carry, pure, boolByte, Sum.elim]

theorem terminates (s : X86State) :
    ∃ out, Add128.execute 5 s = some out ∧ Post s out :=
  finishes_execute Add128.step (Add128.initial s) (Post s) (completion s)

theorem correct (s : X86State) : (Add128.run s).wp (Post s) :=
  finishes_run Add128.step (Add128.initial s) (Post s) (completion s)

end Examples.Add128Proof
