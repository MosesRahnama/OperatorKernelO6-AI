import OperatorKernelO6.Kernel
import Init.WF                                  -- WellFounded, InvImage.wf
import Mathlib.Data.Prod.Lex                    -- Prod.Lex, WellFounded.prod_lex
import Mathlib.SetTheory.Ordinal.Basic          -- omega0_pos, etc.
import Mathlib.SetTheory.Ordinal.Arithmetic     -- Ordinal.add_*, mul_*
import Mathlib.SetTheory.Ordinal.Exponential    -- Ordinal.opow_*, opow_le_opow_right
import Mathlib.Algebra.Order.SuccPred           -- Order.lt_add_one_iff, etc.
import Mathlib.Data.Nat.Cast.Order.Basic        -- Nat.cast_le, Nat.cast_lt
open Ordinal
open OperatorKernelO6
namespace OperatorKernelO6.Meta
open Trace Step

/- κ : RecΔ-nesting depth ---------------------------------------------------/
@[simp] def kappa : Trace → Nat
| Trace.recΔ _ _ _ => 2
| Trace.eqW _ _    => 1
| _                => 0

/- μ : Ordinal measure from Termination_C ------------------------------------/
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

/- Combined lexicographic measure ------------------------------------------/
@[simp] noncomputable def mu_kappa (t : Trace) : Prod Nat Ordinal :=
  (kappa t, mu t)

/- Lexicographic order on Nat × Ordinal ------------------------------------/
def LexNatOrd : (Nat × Ordinal) → (Nat × Ordinal) → Prop :=
  Prod.Lex (· < ·) ((· < ·) : Ordinal → Ordinal → Prop)

/- wf_LexNatOrd — Cookbook §1 ----------------------------------------------/
lemma wf_LexNatOrd : WellFounded LexNatOrd := by
  unfold LexNatOrd
  exact WellFounded.prod_lex wellFounded_lt Ordinal.lt_wf

/- μ-drop ⇒ (κ, μ)-drop — Cookbook §2 ---------------------------------------/
lemma mu_to_mu_kappa
  {t t' : Trace} (hμ : mu t' < mu t) (hκ : kappa t' = kappa t) :
  LexNatOrd (mu_kappa t') (mu_kappa t) := by
  unfold LexNatOrd mu_kappa
  rw [hκ]
  apply Prod.Lex.right
  exact hμ

/- recΔ succ case — Cookbook §3 ---------------------------------------------/
lemma mu_kappa_lt_R_rec_succ (b s n : Trace) :
  LexNatOrd (mu_kappa (merge s (recΔ b s n))) (mu_kappa (recΔ b s (delta n))) := by
  unfold LexNatOrd mu_kappa
  -- κ drops from 2 (for `recΔ`) to 0 (for `merge`), independent of the inner `n`
  apply Prod.Lex.left
  simp [kappa]

/- ... seven more decrease lemmas go here (copy-pattern) --------------------/

-- lemma mu_kappa_decreases : ∀ {t u}, Step t u →
--   Prod.Lex Nat.lt Ordinal.< (mu_kappa u) (mu_kappa t) := by
--   -- TODO (Cookbook §7)

/- Main SN theorem via InvImage.wf — Cookbook §8 ----------------------------/
-- theorem strong_normalization_lex : WellFounded (fun a b => Step b a) := by
--   -- have wf := InvImage.wf (f := mu_kappa) wf_LexNatOrd
--   -- exact Subrelation.wf mu_kappa_decreases wf

end OperatorKernelO6.Meta
