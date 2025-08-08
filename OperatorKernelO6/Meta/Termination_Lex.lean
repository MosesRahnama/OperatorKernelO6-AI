import OperatorKernelO6.Kernel
import Init.WF
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic
-- import OperatorKernelO6.Meta.Termination_C  -- Temporarily commented out due to conflicts


set_option linter.unnecessarySimpa false

universe u

open Ordinal
open OperatorKernelO6
open Trace
-- open MetaSN  -- Commented out since we're not importing Termination_C

namespace MetaSN  -- Our own clean namespace



/-- Local κ for the lexicographic measure: only the outer shape matters.
    This avoids relying on internal structure of `b` in `R_rec_zero`. -/
@[simp] def klex : Trace → Nat
| Trace.recΔ _ _ _ => 1
| Trace.eqW _ _    => 1
| _                => 0

noncomputable def mu : Trace → Ordinal.{0}
| .void        => 0
| .delta t     => (omega0 ^ (5 : Ordinal)) * (mu t + 1) + 1
| .integrate t => (omega0 ^ (4 : Ordinal)) * (mu t + 1) + 1
| .merge a b   =>
    (omega0 ^ (3 : Ordinal)) * (mu a + 1) +
    (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 1
| .recΔ b s n  =>
    omega0 ^ (mu n + mu s + (6 : Ordinal))
  + omega0 * (mu b + 1) + 1
| .eqW a b     =>
    omega0 ^ (mu a + mu b + (9 : Ordinal)) + 1
@[simp] noncomputable abbrev mu_kappa : Trace → Nat × Ordinal := fun t => (klex t, mu t)

/-- Lexicographic order on `ℕ × Ordinal`.  -/
@[simp] def LexNatOrd : (Nat × Ordinal) → (Nat × Ordinal) → Prop :=
  Prod.Lex (· < ·) ((· < ·) : Ordinal → Ordinal → Prop)

/-- Well-foundedness of `LexNatOrd`.  Cook-book §1. -/
lemma wf_LexNatOrd : WellFounded LexNatOrd := by
  unfold LexNatOrd
  exact WellFounded.prod_lex wellFounded_lt Ordinal.lt_wf

/-- Lift a strict μ-drop to the lexicographic order when κ is unchanged.  Cook-book §2. -/
lemma mu_to_mu_kappa {t t' : Trace} (hμ : mu t' < mu t) (hκ : klex t' = klex t) :
    LexNatOrd (mu_kappa t') (mu_kappa t) := by
  unfold LexNatOrd mu_kappa
  rw [hκ]
  exact Prod.Lex.right _ hμ

/-- Successor case of the recursor: κ drops.  Cook-book §3. -/
lemma mu_kappa_lt_R_rec_succ (b s n : Trace) :
    LexNatOrd (mu_kappa (merge s (recΔ b s n)))
              (mu_kappa (recΔ b s (delta n))) := by
  unfold LexNatOrd mu_kappa
  -- κ(recΔ … δ n) = (κ (delta n)).succ = 1, whereas κ(merge …) = 0.
  apply Prod.Lex.left
  simp [klex]

/-- Main decrease lemma covering **all** eight `Step` constructors.  Cook-book §7. -/
lemma mu_kappa_decreases {t u : Trace} (h : Step t u) :
    LexNatOrd (mu_kappa u) (mu_kappa t) := by
  cases h with
  | R_int_delta t' =>
      have hμ := mu_void_lt_integrate_delta t'
      have hκ : klex (.void) = klex (integrate (delta t')) := by simp [klex]
      exact mu_to_mu_kappa hμ hκ
  | R_merge_void_left t' =>
      have hμ := mu_lt_merge_void_left t'
      have hκ : klex t' = klex (merge .void t') := by simp [klex]
      exact mu_to_mu_kappa hμ hκ
  | R_merge_void_right t' =>
      have hμ := mu_lt_merge_void_right t'
      have hκ : klex t' = klex (merge t' .void) := by simp [klex]
      exact mu_to_mu_kappa hμ hκ
  | R_merge_cancel t' =>
      have hμ := mu_lt_merge_cancel t'
      have hκ : klex t' = klex (merge t' t') := by simp [klex]
      exact mu_to_mu_kappa hμ hκ
  | R_rec_zero b s =>
      -- κ(recΔ … void) = 1 and klex b ∈ {0,1}. Split: equal → μ-drop; else κ-drop.
      have k_rec : klex (recΔ b s void) = 1 := by simp [klex]
      have hb_le : klex b ≤ 1 := by
        cases b <;> simp [klex]
      by_cases hb1 : klex b = 1
      · -- κ equal → use μ-drop on μ-coordinate
        have hμ := mu_lt_rec_zero b s
        unfold LexNatOrd mu_kappa
        apply Prod.Lex.right
        simpa [hb1, k_rec]
          using hμ
      · -- κ unequal but ≤ 1 ⇒ κ b = 0 ⇒ left-coordinate drop
        have hb0 : klex b = 0 := by
          have : klex b < 1 := lt_of_le_of_ne hb_le hb1
          simpa [Nat.lt_one_iff] using this
        unfold LexNatOrd mu_kappa
        apply Prod.Lex.left
        simpa [hb0, k_rec, Nat.zero_lt_one]
  | R_rec_succ b s n =>
      exact mu_kappa_lt_R_rec_succ b s n
  | R_eq_refl a =>
      have hμ := mu_void_lt_eq_refl a
      have hκ : klex (.void) = klex (eqW a a) := by simp [klex]
      exact mu_to_mu_kappa hμ hκ
  | R_eq_diff a b hneq =>
      -- κ drops: 1 → 0
      unfold LexNatOrd mu_kappa
      apply Prod.Lex.left
      simp [klex]

/-- **Strong normalisation** of `Step` via the lexicographic measure.  Cook-book §8. -/
 theorem strong_normalization_lex : WellFounded (fun a b : Trace => Step b a) := by
  have wf := InvImage.wf (f := mu_kappa) wf_LexNatOrd
  exact Subrelation.wf mu_kappa_decreases wf

end MetaSN
