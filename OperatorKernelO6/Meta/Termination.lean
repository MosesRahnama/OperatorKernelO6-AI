import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.TerminationBase
import Init.WF
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic
-- import diagnostics

open Ordinal
open OperatorKernelO6
open Trace

namespace MetaSN








-- IMPORTNAT NOTES:
--- Drop in the three corrected lemmas above replacing their broken predecessors.
--- Ensure merge_inner_bound_simple is used exactly as shown in mu_lt_eq_diff via simpa [hC] using merge_inner_bound_simple a b.
--- Make sure the case split on (void, void) is first so you don’t rely on ω ≤ C there.
--- No new axioms or external lemmas are introduced—all used names must already exist in the base setup.
--- Run the file. If any sub-have fails, the localized name will tell you which inequality needs adjustment and you can cross-reference the working pattern in TerminationBase.lean.


--Note: The below lemma merge_inner_bound_simple uses only existing lemmas: termA_le, termB_le, opow_lt_opow_right, and omega_pow_add3_lt.
--It avoids manually juggling ordinal addition equalities.

/-- Inner bound used by `mu_lt_eq_diff`. Let `C = μ a + μ b`. Then `μ (merge a b) + 1 < ω^(C + 5)`. -/
private theorem merge_inner_bound_simple (a b : Trace) :
  let C : Ordinal := mu a + mu b;
  mu (merge a b) + 1 < omega0 ^ (C + 5) := by
  let C := mu a + mu b
  -- head and tail bounds
  have h_head : (omega0 ^ (3 : Ordinal)) * (mu a + 1) ≤ omega0 ^ (mu a + 4) := termA_le (x := mu a)
  have h_tail : (omega0 ^ (2 : Ordinal)) * (mu b + 1) ≤ omega0 ^ (mu b + 3) := termB_le (x := mu b)
  -- each exponent is strictly less than C+5
  have h_exp1 : mu a + 4 < C + 5 := by
    have h1 : mu a ≤ C := Ordinal.le_add_right _ _
    have h2 : mu a + 4 ≤ C + 4 := add_le_add_right h1 4
    have h3 : C + 4 < C + 5 := add_lt_add_left (by norm_num : (4 : Ordinal) < 5) C
    exact lt_of_le_of_lt h2 h3
  have h_exp2 : mu b + 3 < C + 5 := by
    have h1 : mu b ≤ C := Ordinal.le_add_left (mu b) (mu a)
    have h2 : mu b + 3 ≤ C + 3 := add_le_add_right h1 3
    have h3 : C + 3 < C + 5 := add_lt_add_left (by norm_num : (3 : Ordinal) < 5) C
    exact lt_of_le_of_lt h2 h3
  -- use monotonicity of opow
  have h1_pow : omega0 ^ (3 : Ordinal) * (mu a + 1) < omega0 ^ (C + 5) := by
    calc (omega0 ^ (3 : Ordinal)) * (mu a + 1)
        ≤ omega0 ^ (mu a + 4) := h_head
      _ < omega0 ^ (C + 5) := opow_lt_opow_right h_exp1
  have h2_pow : (omega0 ^ (2 : Ordinal)) * (mu b + 1) < omega0 ^ (C + 5) := by
    calc (omega0 ^ (2 : Ordinal)) * (mu b + 1)
        ≤ omega0 ^ (mu b + 3) := h_tail
      _ < omega0 ^ (C + 5) := opow_lt_opow_right h_exp2
  -- finite +2 is below ω^(C+5)
  have h_fin : (2 : Ordinal) < omega0 ^ (C + 5) := by
    have two_lt_omega : (2 : Ordinal) < omega0 := nat_lt_omega0 2
    have omega_le : omega0 ≤ omega0 ^ (C + 5) := by
      have one_le_exp : (1 : Ordinal) ≤ C + 5 := by
        have : (1 : Ordinal) ≤ (5 : Ordinal) := by norm_num
        exact le_trans this (le_add_left _ _)
      -- Use the fact that ω = ω^1 ≤ ω^(C+5) when 1 ≤ C+5
      calc omega0
          = omega0 ^ (1 : Ordinal) := (Ordinal.opow_one omega0).symm
        _ ≤ omega0 ^ (C + 5) := Ordinal.opow_le_opow_right omega0_pos one_le_exp
    exact lt_of_lt_of_le two_lt_omega omega_le
  -- combine: μ(merge a b)+1 = ω³*(μa+1) + ω²*(μb+1) + 2 < ω^(C+5)
  have sum_bound : (omega0 ^ (3 : Ordinal)) * (mu a + 1) +
                   (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 2 <
                   omega0 ^ (C + 5) := by
    -- use omega_pow_add3_lt with the three smaller pieces
    have k_pos : (0 : Ordinal) < C + 5 := by
      have : (0 : Ordinal) < (5 : Ordinal) := by norm_num
      exact lt_of_lt_of_le this (le_add_left _ _)
    -- we need three inequalities of the form ω^something < ω^(C+5) and 2 < ω^(C+5)
    exact omega_pow_add3_lt k_pos h1_pow h2_pow h_fin
  -- relate to mu (merge a b)+1
  have mu_def : mu (merge a b) + 1 = (omega0 ^ (3 : Ordinal)) * (mu a + 1) +
                                     (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 2 := by
    simp [mu]
  simpa [mu_def] using sum_bound


/-- Concrete inequality for the `(void,void)` pair. -/
theorem mu_lt_eq_diff_both_void :
  mu (integrate (merge .void .void)) < mu (eqW .void .void) := by
  -- inner numeric bound: ω³ + ω² + 2 < ω⁵
  have h_inner :
      omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2 <
      omega0 ^ (5 : Ordinal) := by
    have h3 : omega0 ^ (3 : Ordinal) < omega0 ^ (5 : Ordinal) := opow_lt_opow_right (by norm_num)
    have h2 : omega0 ^ (2 : Ordinal) < omega0 ^ (5 : Ordinal) := opow_lt_opow_right (by norm_num)
    have h_fin : (2 : Ordinal) < omega0 ^ (5 : Ordinal) := by
      have two_lt_omega : (2 : Ordinal) < omega0 := nat_lt_omega0 2
      have omega_le : omega0 ≤ omega0 ^ (5 : Ordinal) := by
        have : (1 : Ordinal) ≤ (5 : Ordinal) := by norm_num
        calc omega0
            = omega0 ^ (1 : Ordinal) := (Ordinal.opow_one omega0).symm
          _ ≤ omega0 ^ (5 : Ordinal) := Ordinal.opow_le_opow_right omega0_pos this
      exact lt_of_lt_of_le two_lt_omega omega_le
    exact omega_pow_add3_lt (by norm_num : (0 : Ordinal) < 5) h3 h2 h_fin
  -- multiply by ω⁴ to get ω⁹
  have h_prod :
      omega0 ^ (4 : Ordinal) * (mu (merge .void .void) + 1) <
      omega0 ^ (9 : Ordinal) := by
    have rew : mu (merge .void .void) + 1 = omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2 := by simp [mu]
    rw [rew]
    -- The goal is ω^4 * (ω^3 + ω^2 + 2) < ω^9, we know ω^3 + ω^2 + 2 < ω^5
    -- So ω^4 * (ω^3 + ω^2 + 2) < ω^4 * ω^5 = ω^9
    have h_bound : omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2 < omega0 ^ (5 : Ordinal) := h_inner
    have h_mul : omega0 ^ (4 : Ordinal) * (omega0 ^ (3 : Ordinal) + omega0 ^ (2 : Ordinal) + 2) <
                 omega0 ^ (4 : Ordinal) * omega0 ^ (5 : Ordinal) :=
      Ordinal.mul_lt_mul_of_pos_left h_bound (Ordinal.opow_pos (b := (4 : Ordinal)) omega0_pos)
    -- Use opow_add: ω^4 * ω^5 = ω^(4+5) = ω^9
    have h_exp : omega0 ^ (4 : Ordinal) * omega0 ^ (5 : Ordinal) = omega0 ^ (9 : Ordinal) := by
      rw [←opow_add]
      norm_num
    rw [h_exp] at h_mul
    exact h_mul
  -- add +1 and finish
  have h_core :
      omega0 ^ (4 : Ordinal) * (mu (merge .void .void) + 1) + 1 <
      omega0 ^ (9 : Ordinal) + 1 := by
    exact lt_add_one_of_le (Order.add_one_le_of_lt h_prod)
  simp [mu] at h_core
  simpa [mu] using h_core




/-- Any non-void trace has `μ ≥ ω`.  Exhaustive on constructors. -/
private theorem nonvoid_mu_ge_omega {t : Trace} (h : t ≠ .void) :
    omega0 ≤ mu t := by
  cases t with
  | void        => exact (h rfl).elim

  | delta s =>
      -- ω ≤ ω⁵ ≤ ω⁵·(μ s + 1) + 1
      have hω_pow : omega0 ≤ omega0 ^ (5 : Ordinal) :=
        Ordinal.opow_le_opow_right omega0_pos (by norm_num)
      have h_one_le : (1 : Ordinal) ≤ mu s + 1 := by
        have : (0 : Ordinal) ≤ mu s := zero_le _
        simpa [zero_add] using add_le_add_right this 1
      have hmul :
          omega0 ^ (5 : Ordinal) ≤ (omega0 ^ (5 : Ordinal)) * (mu s + 1) := by
        simpa [mul_one] using
          mul_le_mul_left' h_one_le (omega0 ^ (5 : Ordinal))
      have : omega0 ≤ mu (.delta s) := by
        calc
          omega0 ≤ omega0 ^ (5 : Ordinal) := hω_pow
          _      ≤ (omega0 ^ (5 : Ordinal)) * (mu s + 1) := hmul
          _      ≤ (omega0 ^ (5 : Ordinal)) * (mu s + 1) + 1 :=
                   le_add_of_nonneg_right (zero_le _)
          _      = mu (.delta s) := by simp [mu]
      simpa [mu, add_comm, add_left_comm, add_assoc] using this

  | integrate s =>
      -- ω ≤ ω⁴ ≤ ω⁴·(μ s + 1) + 1
      have hω_pow : omega0 ≤ omega0 ^ (4 : Ordinal) :=
        Ordinal.opow_le_opow_right omega0_pos (by norm_num)
      have h_one_le : (1 : Ordinal) ≤ mu s + 1 := by
        have : (0 : Ordinal) ≤ mu s := zero_le _
        simpa [zero_add] using add_le_add_right this 1
      have hmul :
          omega0 ^ (4 : Ordinal) ≤ (omega0 ^ (4 : Ordinal)) * (mu s + 1) := by
        simpa [mul_one] using
          mul_le_mul_left' h_one_le (omega0 ^ (4 : Ordinal))
      have : omega0 ≤ mu (.integrate s) := by
        calc
          omega0 ≤ omega0 ^ (4 : Ordinal) := hω_pow
          _      ≤ (omega0 ^ (4 : Ordinal)) * (mu s + 1) := hmul
          _      ≤ (omega0 ^ (4 : Ordinal)) * (mu s + 1) + 1 :=
                   le_add_of_nonneg_right (zero_le _)
          _      = mu (.integrate s) := by simp [mu]
      simpa [mu, add_comm, add_left_comm, add_assoc] using this

  | merge a b =>
      -- ω ≤ ω² ≤ ω²·(μ b + 1) ≤ μ(merge a b)
      have hω_pow : omega0 ≤ omega0 ^ (2 : Ordinal) :=
        Ordinal.opow_le_opow_right omega0_pos (by norm_num)
      have h_one_le : (1 : Ordinal) ≤ mu b + 1 := by
        have : (0 : Ordinal) ≤ mu b := zero_le _
        simpa [zero_add] using add_le_add_right this 1
      have hmul :
          omega0 ^ (2 : Ordinal) ≤ (omega0 ^ (2 : Ordinal)) * (mu b + 1) := by
        simpa [mul_one] using
          mul_le_mul_left' h_one_le (omega0 ^ (2 : Ordinal))
      have h_mid :
          omega0 ≤ (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 1 := by
        calc
          omega0 ≤ (omega0 ^ (2 : Ordinal)) * (mu b + 1) := hmul
          _      ≤ (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 1 :=
                   le_add_of_nonneg_right (zero_le _)
      have : omega0 ≤ mu (.merge a b) := by
        have h_left_nonneg :
            (0 : Ordinal) ≤ (omega0 ^ (3 : Ordinal)) * (mu a + 1) :=
          zero_le _
        exact
          le_trans h_mid
            (le_add_of_nonneg_left
              (le_add_of_nonneg_left h_left_nonneg))
      simpa [mu, add_comm, add_left_comm, add_assoc] using this

  | recΔ b s n =>
      -- ω ≤ ω^(μ n + μ s + 6) ≤ μ(recΔ b s n)
      have six_le : (6 : Ordinal) ≤ mu n + mu s + 6 := by
        have : (0 : Ordinal) ≤ mu n + mu s :=
          add_nonneg (zero_le _) (zero_le _)
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right this 6
      have one_le : (1 : Ordinal) ≤ mu n + mu s + 6 :=
        le_trans (by norm_num) six_le
      have hω_pow : omega0 ≤ omega0 ^ (mu n + mu s + 6) := by
        simpa [Ordinal.opow_one] using
          Ordinal.opow_le_opow_right omega0_pos one_le
      have : omega0 ≤ mu (.recΔ b s n) := by
        calc
          omega0 ≤ omega0 ^ (mu n + mu s + 6) := hω_pow
          _      ≤ omega0 ^ (mu n + mu s + 6) + omega0 * (mu b + 1) :=
                   le_add_of_nonneg_right (zero_le _)
          _      ≤ omega0 ^ (mu n + mu s + 6) + omega0 * (mu b + 1) + 1 :=
                   le_add_of_nonneg_right (zero_le _)
          _      = mu (.recΔ b s n) := by simp [mu]
      simpa [mu, add_comm, add_left_comm, add_assoc] using this

  | eqW a b =>
      -- ω ≤ ω^(μ a + μ b + 9) ≤ μ(eqW a b)
      have nine_le : (9 : Ordinal) ≤ mu a + mu b + 9 := by
        have : (0 : Ordinal) ≤ mu a + mu b :=
          add_nonneg (zero_le _) (zero_le _)
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right this 9
      have one_le : (1 : Ordinal) ≤ mu a + mu b + 9 :=
        le_trans (by norm_num) nine_le
      have hω_pow : omega0 ≤ omega0 ^ (mu a + mu b + 9) := by
        simpa [Ordinal.opow_one] using
          Ordinal.opow_le_opow_right omega0_pos one_le
      have : omega0 ≤ mu (.eqW a b) := by
        calc
          omega0 ≤ omega0 ^ (mu a + mu b + 9) := hω_pow
          _      ≤ omega0 ^ (mu a + mu b + 9) + 1 :=
                   le_add_of_nonneg_right (zero_le _)
          _      = mu (.eqW a b) := by simp [mu]
      simpa [mu, add_comm, add_left_comm, add_assoc] using this


/-- If `a` and `b` are **not** both `void`, then `ω ≤ μ a + μ b`. -/
theorem mu_sum_ge_omega_of_not_both_void
    {a b : Trace} (h : ¬ (a = .void ∧ b = .void)) :
    omega0 ≤ mu a + mu b := by
  have h_cases : a ≠ .void ∨ b ≠ .void := by
    by_contra hcontra; push_neg at hcontra; exact h hcontra
  cases h_cases with
  | inl ha =>
      have : omega0 ≤ mu a := nonvoid_mu_ge_omega ha
      have : omega0 ≤ mu a + mu b :=
        le_trans this (le_add_of_nonneg_right (zero_le _))
      exact this
  | inr hb =>
      have : omega0 ≤ mu b := nonvoid_mu_ge_omega hb
      have : omega0 ≤ mu a + mu b :=
        le_trans this (le_add_of_nonneg_left (zero_le _))
      exact this

/-- Total inequality used in `R_eq_diff`. -/
theorem mu_lt_eq_diff (a b : Trace) :
    mu (integrate (merge a b)) < mu (eqW a b) := by
  by_cases h_both : a = .void ∧ b = .void
  · rcases h_both with ⟨ha, hb⟩
    -- corner case already proven
    simpa [ha, hb] using mu_lt_eq_diff_both_void
  · -- general case
    set C : Ordinal := mu a + mu b with hC
    have hCω : omega0 ≤ C :=
      by
        have := mu_sum_ge_omega_of_not_both_void (a := a) (b := b) h_both
        simpa [hC] using this

    -- inner bound from `merge_inner_bound_simple`
    have h_inner : mu (merge a b) + 1 < omega0 ^ (C + 5) :=
      by
        simpa [hC] using merge_inner_bound_simple a b

    -- lift through `integrate`
    have ω4pos : 0 < omega0 ^ (4 : Ordinal) :=
      (Ordinal.opow_pos (b := (4 : Ordinal)) omega0_pos)
    have h_mul :
        omega0 ^ (4 : Ordinal) * (mu (merge a b) + 1) <
        omega0 ^ (4 : Ordinal) * omega0 ^ (C + 5) :=
      Ordinal.mul_lt_mul_of_pos_left h_inner ω4pos

    -- collapse ω⁴·ω^(C+5)  →  ω^(4+(C+5))
    have h_prod :
        omega0 ^ (4 : Ordinal) * (mu (merge a b) + 1) <
        omega0 ^ (4 + (C + 5)) :=
      by
        have := (opow_add (a := omega0) (b := (4 : Ordinal)) (c := C + 5)).symm
        simpa [this] using h_mul

    -- absorb the finite 4 because ω ≤ C
    have absorb4 : (4 : Ordinal) + C = C :=
      nat_left_add_absorb (h := hCω)
    have exp_eq : (4 : Ordinal) + (C + 5) = C + 5 := by
      calc
        (4 : Ordinal) + (C + 5)
            = ((4 : Ordinal) + C) + 5 := by
                simpa [add_assoc]
          _ = C + 5 := by
                simpa [absorb4]

    -- inequality now at exponent C+5
    have h_prod2 :
        omega0 ^ (4 : Ordinal) * (mu (merge a b) + 1) <
        omega0 ^ (C + 5) := by
      simpa [exp_eq] using h_prod

    -- bump exponent C+5 → C+9
    have exp_lt : omega0 ^ (C + 5) < omega0 ^ (C + 9) :=
      opow_lt_opow_right (add_lt_add_left (by norm_num) C)

    have h_chain :
        omega0 ^ (4 : Ordinal) * (mu (merge a b) + 1) <
        omega0 ^ (C + 9) := lt_trans h_prod2 exp_lt

    -- add outer +1 and rewrite both μ’s
    have h_final :
        omega0 ^ (4 : Ordinal) * (mu (merge a b) + 1) + 1 <
        omega0 ^ (C + 9) + 1 :=
      lt_add_one_of_le (Order.add_one_le_of_lt h_chain)

    simpa [mu, hC] using h_final




-- theorem mu_decreases :
--   ∀ {a b : Trace}, OperatorKernelO6.Step a b → mu b < mu a := by
--   intro a b h
--   cases h with
--   | @R_int_delta t          => simpa using mu_void_lt_integrate_delta t
--   | R_merge_void_left       => simpa using mu_lt_merge_void_left  b
--   | R_merge_void_right      => simpa using mu_lt_merge_void_right b
--   | R_merge_cancel          => simpa using mu_lt_merge_cancel     b
--   | @R_rec_zero _ _         => simpa using mu_lt_rec_zero _ _
--   | @R_rec_succ b s n       => exact mu_lt_rec_succ b s n
--   | @R_eq_refl a            => simpa using mu_void_lt_eq_refl a
--   | @R_eq_diff a b _        => exact mu_lt_eq_diff a b

-- def StepRev (R : Trace → Trace → Prop) : Trace → Trace → Prop := fun a b => R b a

-- theorem strong_normalization_forward_trace
--   (R : Trace → Trace → Prop)
--   (hdec : ∀ {a b : Trace}, R a b → mu b < mu a) :
--   WellFounded (StepRev R) := by
--   have hwf : WellFounded (fun x y : Trace => mu x < mu y) :=
--     InvImage.wf (f := mu) (h := Ordinal.lt_wf)
--   have hsub : Subrelation (StepRev R) (fun x y : Trace => mu x < mu y) := by
--     intro x y h; exact hdec (a := y) (b := x) h
--   exact Subrelation.wf hsub hwf

-- theorem strong_normalization_backward
--   (R : Trace → Trace → Prop)
--   (hinc : ∀ {a b : Trace}, R a b → mu a < mu b) :
--   WellFounded R := by
--   have hwf : WellFounded (fun x y : Trace => mu x < mu y) :=
--     InvImage.wf (f := mu) (h := Ordinal.lt_wf)
--   have hsub : Subrelation R (fun x y : Trace => mu x < mu y) := by
--     intro x y h
--     exact hinc h
--   exact Subrelation.wf hsub hwf

-- def KernelStep : Trace → Trace → Prop := fun a b => OperatorKernelO6.Step a b

-- theorem step_strong_normalization : WellFounded (StepRev KernelStep) := by
--   refine Subrelation.wf ?hsub (InvImage.wf (f := mu) (h := Ordinal.lt_wf))
--   intro x y hxy
--   have hk : KernelStep y x := hxy
--   have hdec : mu x < mu y := mu_decreases hk
--   exact hdec

end MetaSN
