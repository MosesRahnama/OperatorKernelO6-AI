import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Termination_C
import Init.WF                                  -- WellFounded, InvImage.wf
import Mathlib.Data.Prod.Lex                    -- Prod.Lex, WellFounded.prod_lex
import Mathlib.SetTheory.Ordinal.Basic          -- omega0_pos, etc.
import Mathlib.SetTheory.Ordinal.Arithmetic     -- Ordinal.add_*, mul_*
import Mathlib.SetTheory.Ordinal.Exponential    -- Ordinal.opow_*, opow_le_opow_right
import Mathlib.Algebra.Order.SuccPred           -- Order.lt_add_one_iff, etc.
import Mathlib.Data.Nat.Cast.Order.Basic        -- Nat.cast_le, Nat.cast_lt

open Ordinal
open OperatorKernelO6
open MetaSN

namespace Meta

/- Helper lemma for the `R_rec_zero` case -------------------------------------/
@[simp] lemma kappa_rec_zero_bound (b s : Trace) : kappa b ≤ 1 := by
  cases b <;> simp [kappa]

/- Main lemma: combined (κ, μ) measure strictly decreases for every Step -----/

theorem mu_kappa_decreases_lex :
  ∀ {a b : Trace}, Step a b → LexNatOrd (μκ b) (μκ a) := by
  intro a b h
  cases h with
  | @R_int_delta t =>
      have h_mu : mu .void < mu (integrate (delta t)) := mu_void_lt_integrate_delta t
      have h_kappa : kappa .void = kappa (integrate (delta t)) := by simp [kappa]
      exact μ_to_μκ h_mu h_kappa
  | R_merge_void_left =>
      have h_mu : mu b < mu (merge .void b) := mu_lt_merge_void_left b
      have h_kappa : kappa b = kappa (merge .void b) := by simp [kappa]
      exact μ_to_μκ h_mu h_kappa
  | R_merge_void_right =>
      have h_mu : mu b < mu (merge b .void) := mu_lt_merge_void_right b
      have h_kappa : kappa b = kappa (merge b .void) := by simp [kappa]
      exact μ_to_μκ h_mu h_kappa
  | R_merge_cancel =>
      have h_mu : mu b < mu (merge b b) := mu_lt_merge_cancel b
      have h_kappa : kappa b = kappa (merge b b) := by simp [kappa]
      exact μ_to_μκ h_mu h_kappa
  | @R_rec_zero b s =>
      -- κ(recΔ … void) = 1. Distinguish whether κ b is 0 or 1.
      have k_rec : kappa (recΔ b s .void) = 1 := by simp [kappa]
      have hb_le : kappa b ≤ 1 := kappa_rec_zero_bound b s
      by_cases h_eq : kappa b = 1
      · -- κ equal ⇒ use μ decrease
        have h_mu := mu_lt_rec_zero b s
        have h_kappa : kappa b = kappa (recΔ b s .void) := by simpa [h_eq, k_rec]
        exact μ_to_μκ h_mu h_kappa
      · -- κ drops from 1 to 0
        have hb0 : kappa b = 0 := by
          have : kappa b < 1 := lt_of_le_of_ne hb_le h_eq
          simpa [Nat.lt_one_iff] using this
        unfold LexNatOrd μκ
        apply Prod.Lex.left
        simp [hb0, k_rec, Nat.zero_lt_one]
  | @R_eq_refl a =>
      have h_mu : mu .void < mu (eqW a a) := mu_void_lt_eq_refl a
      have h_kappa : kappa .void = kappa (eqW a a) := by simp [kappa]
      exact μ_to_μκ h_mu h_kappa
  | @R_eq_diff a b _ =>
      have h_mu : mu (integrate (merge a b)) < mu (eqW a b) := mu_lt_eq_diff a b
      have h_kappa : kappa (integrate (merge a b)) = kappa (eqW a b) := by simp [kappa]
      exact μ_to_μκ h_mu h_kappa
  | R_rec_succ b s n =>
      -- κ strictly drops in R_rec_succ (no numeric bound needed)
      exact μκ_lt_R_rec_succ b s n

/- Strong normalization via the lexicographic measure -------------------------/

theorem strong_normalization_lex : WellFounded (fun a b => Step b a) := by
  have wf_lex : WellFounded LexNatOrd := wf_LexNatOrd
  refine Subrelation.wf ?hsub (InvImage.wf (f := μκ) wf_lex)
  intro x y hxy
  have hdec : LexNatOrd (μκ x) (μκ y) := mu_kappa_decreases_lex hxy
  exact hdec

end Meta
`