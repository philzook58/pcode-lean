import Std.WP
import Std.Tactic.Do

/-! Deterministic assembly blocks, unbounded partial correctness, and separate termination proofs.
The decoder rejects unsupported effects before generating a program. -/
namespace PcodeLean
open Std.WP Lean.Order
set_option experimental.vcgen true

/-- Continue at a generated instruction boundary, or return the final machine state. -/
abbrev Step (σ α : Type) := σ → Id (Sum σ α)

/-- Return postcondition for every execution prefix of the given length. -/
def safe (step : Step σ α) : Nat → σ → (α → Prop) → Prop
  | 0, _, _ => True
  | n + 1, s, Q => Sum.elim (fun s' ↦ safe step n s' Q) Q (step s)

theorem safe_mono (step : Step σ α) (n : Nat) (s : σ)
    (h : ∀ a, P a → Q a) : safe step n s P → safe step n s Q := by
  induction n generalizing s with
  | zero => exact id
  | succ n ih =>
    simp only [safe]
    cases step s with
    | inl s' => exact ih s'
    | inr a => exact h a

/-- A specification for every finite execution prefix. This alone does not assert termination. -/
structure Program (α : Type) where
  wp : (α → Prop) → Prop
  mono : ∀ {P Q}, (∀ a, P a → Q a) → wp P → wp Q

instance : WP (Program α) α Prop EStack⟨⟩ where
  wpTrans p := ⟨fun Q _ ↦ p.wp Q⟩
  wp_trans_monotone p := fun _ _ _ _ _ h ↦ p.mono h

def run (step : Step σ α) (initial : σ) : Program α where
  wp Q := ∀ n, safe step n initial Q
  mono h hx n := safe_mono step n initial h (hx n)

/-- Prove each instruction against a PC-indexed invariant using the standard `vcgen` tactic. -/
@[spec] theorem run_spec (step : Step σ α) (initial : σ) (I : σ → Prop) (Q : α → Prop)
    (preserves : ∀ s, ⦃I s⦄ step s ⦃Sum.elim I Q⦄) :
    ⦃I initial⦄ run step initial ⦃Q⦄ := by
  constructor
  intro hi n
  induction n generalizing initial with
  | zero => trivial
  | succ n ih =>
    have h := (preserves initial).le_wp hi
    change Sum.elim I Q (step initial) at h
    simp only [safe]
    cases heq : step initial with
    | inl s' => simp only [heq, Sum.elim_inl] at h ⊢; exact ih s' h
    | inr a => simpa only [heq, Sum.elim_inr] using h

/-- Fuel exhaustion is `none`, never a successful execution. -/
def execute (step : Step σ α) : Nat → σ → Option α
  | 0, _ => none
  | n + 1, s => match step s with
    | .inl s' => execute step n s'
    | .inr a => some a

/-- The same generated step function is used for proofs and concrete execution. -/
theorem execute_correct (step : Step σ α) (s : σ) (Q : α → Prop)
    (h : (run step s).wp Q) (he : execute step n s = some a) : Q a := by
  have hs := h n
  clear h
  induction n generalizing s with
  | zero => simp [execute] at he
  | succ n ih =>
    simp only [execute] at he
    simp only [safe] at hs
    cases heq : step s with
    | inl s' =>
      simp only [heq, Sum.elim_inl] at hs he
      exact ih s' he hs
    | inr value =>
      simp only [heq, Sum.elim_inr, Option.some.injEq] at hs he
      subst a
      exact hs

/-- Every feasible execution returns within the given number of instruction boundaries. -/
def finishes (step : Step σ α) : Nat → σ → (α → Prop) → Prop
  | 0, _, _ => False
  | n + 1, s, Q => Sum.elim (fun s' ↦ finishes step n s' Q) Q (step s)

theorem finishes_mono (step : Step σ α) {a b : Nat} (h : a ≤ b) (s : σ) (Q : α → Prop) :
    finishes step a s Q → finishes step b s Q := by
  induction a generalizing b s with
  | zero => exact False.elim
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      simp only [finishes]
      cases step s with
      | inl s' => exact ih (by omega) s'
      | inr _ => exact id

theorem finishes_execute (step : Step σ α) (s : σ) (Q : α → Prop)
    (h : finishes step n s Q) : ∃ a, execute step n s = some a ∧ Q a := by
  induction n generalizing s with
  | zero => exact False.elim h
  | succ n ih =>
    simp only [finishes] at h
    simp only [execute]
    cases heq : step s with
    | inl s' =>
      simp only [heq, Sum.elim_inl] at h ⊢
      exact ih s' h
    | inr a =>
      simp only [heq, Sum.elim_inr] at h ⊢
      exact ⟨a, rfl, h⟩

theorem finishes_run (step : Step σ α) (s : σ) (Q : α → Prop)
    (h : finishes step n s Q) : (run step s).wp Q := by
  intro k
  induction n generalizing s k with
  | zero => exact False.elim h
  | succ n ih =>
    cases k with
    | zero => trivial
    | succ k =>
      simp only [finishes] at h
      simp only [safe]
      cases heq : step s with
      | inl s' =>
        simp only [heq, Sum.elim_inl] at h ⊢
        exact ih s' h k
      | inr a => simpa only [heq, Sum.elim_inr] using h

mutual
/-- Every feasible path reaches a state where `stop` holds within `n` steps, without
returning, and that state satisfies `R`. Defined through `after`, which consumes the step's
result, so `simp` only unfolds the next step once the previous one is concrete. It
evaluates `stop` on concrete instruction labels, so a proof can cover one segment at a time. -/
def leadsTo (step : Step σ α) (stop : σ → Bool) : Nat → σ → (σ → Prop) → Prop
  | 0, _, _ => False
  | n + 1, s, R => after step stop n R (step s)
  termination_by n => 2 * n

def after (step : Step σ α) (stop : σ → Bool) (n : Nat) (R : σ → Prop) : Sum σ α → Prop
  | .inl s' => if stop s' then R s' else leadsTo step stop n s' R
  | .inr _ => False
  termination_by 2 * n + 1
end

theorem after_ite {step : Step σ α} {stop : σ → Bool} {n : Nat} {R : σ → Prop} {c : Prop}
    [Decidable c] (a b : Sum σ α) :
    after step stop n R (if c then a else b) = if c then after step stop n R a else after step stop n R b := by
  split <;> rfl

/-- Compose a segment with a proof for the states it stops at. -/
theorem finishes_of_leadsTo (step : Step σ α) (stop : σ → Bool) {R : σ → Prop} {Q : α → Prop}
    {m : Nat} (k : ∀ s, R s → finishes step m s Q) :
    ∀ n s, leadsTo step stop n s R → finishes step (n + m) s Q
  | 0, _, h => by simp [leadsTo] at h
  | n + 1, s, h => by
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [leadsTo] at h
    simp only [finishes]
    cases heq : step s with
    | inr _ => simp [heq, after] at h
    | inl s' =>
      simp only [heq, after] at h
      simp only [Sum.elim_inl]
      split at h
      · exact finishes_mono step (by omega) s' Q (k s' h)
      · exact finishes_of_leadsTo step stop k n s' h

/-- Combine functional correctness with a separately established frame condition. -/
theorem safe_and (step : Step σ α) (n : Nat) (s : σ)
    (hp : safe step n s P) (hq : safe step n s Q) :
    safe step n s (fun a ↦ P a ∧ Q a) := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    simp only [safe] at *
    cases heq : step s with
    | inl s' =>
      simp only [heq, Sum.elim_inl] at hp hq ⊢
      exact ih s' hp hq
    | inr a => simpa only [heq, Sum.elim_inr] using And.intro hp hq

theorem run_and (step : Step σ α) (s : σ)
    (hp : (run step s).wp P) (hq : (run step s).wp Q) :
    (run step s).wp (fun a ↦ P a ∧ Q a) := fun n ↦ safe_and step n s (hp n) (hq n)

/-- A natural-number rank proves termination independently of the partial correctness contract. -/
theorem finishes_of_rank (step : Step σ α) (I : σ → Prop) (rank : σ → Nat) (Q : α → Prop)
    (decreases : ∀ s, I s →
      Sum.elim (fun s' ↦ I s' ∧ rank s' < rank s) Q (step s))
    (s : σ) (hi : I s) : finishes step (rank s + 1) s Q := by
  induction h : rank s using Nat.strongRecOn generalizing s with
  | ind n ih =>
    have hd := decreases s hi
    simp only [finishes]
    cases heq : step s with
    | inr a => simpa only [heq, Sum.elim_inr] using hd
    | inl s' =>
      simp only [heq, Sum.elim_inl] at hd ⊢
      exact finishes_mono step (by omega) s' Q
        (ih (rank s') (by omega) s' hd.1 rfl)

end PcodeLean
