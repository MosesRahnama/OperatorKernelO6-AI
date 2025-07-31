

  § Finishing `mu_merge_lt_rec` 
 lemma mu_merge_lt_rec {b s n : Trace} :
   mu (merge s (recΔ b s n)) < mu (recΔ b s (delta n)) := by
    rename the dominant tower once and for all
   set A : Ordinal := omega0 ^ (mu (delta n) + mu s + 6) with hA
    ❶  head        (ω³ payload)  < A
   have h_head : omega0 ^ (3 : Ordinal) * (mu s + 1) < A := by
     simpa [hA] using head_lt_A s n
    ❷  tail        (ω² payload)  < A  (new lemma)
   have h_tail : omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) < A := by
     simpa [hA] using tail_lt_A (b := b) (s := s) (n := n)
    ❸  sum of head + tail + 1 < A  (principal segment lemma, 3‑term form)
   have h_sum :
       omega0 ^ (3 : Ordinal) * (mu s + 1) +
       (omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) + 1) < A := by
      First fold inner `tail+1` under A.
     have h_tail1 :
         omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) + 1 < A :=
       omega_pow_add_lt (by norm_num) h_tail (by
          `1 < A` trivially (tower is non‑zero)
         have : (1 : Ordinal) < A := by
           have : (0 : Ordinal) < A := opow_pos _ _ omega0_pos
           exact lt_of_le_of_lt (one_le_of_lt this) this
         exact this)
      Then fold head + (tail+1).
     simpa [add_assoc] using
       omega_pow_add_lt (by norm_num) h_head (by
         have := h_tail1; simpa [add_comm] using this)
    ❹  RHS is   A + ω·… + 1  >  A  >  LHS.
   have h_rhs_gt_A : A < mu (recΔ b s (delta n)) := by
      by definition of μ(recΔ … (δ n)) (see new μ)
     have : A < A + omega0 * (mu b + 1) + 1 := by
       have hpos : (0 : Ordinal) < omega0 * (mu b + 1) + 1 := by
         have := le_add_of_nonneg_left (omega0 * (mu b + 1)) (le_of_lt (succ_pos 0))
         exact lt_of_lt_of_le (zero_lt_one) this
       simpa [mu, hA] using lt_add_of_pos_right A hpos
     simpa [mu, hA] using this
    ❺  chain inequalities.
   have : mu (merge s (recΔ b s n)) < A := by
      rewrite μ(merge …) exactly and apply `h_sum`
     have : mu (merge s (recΔ b s n)) =
         omega0 ^ (3 : Ordinal) * (mu s + 1) +
         (omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) + 1) := by
       simp [mu]
     simpa [this] using h_sum
   exact lt_trans this h_rhs_gt_A

  § Simpler wrapper (kept same name for compatibility) 
 @[simp] lemma mu_lt_rec_succ (b s n : Trace) :
   mu (merge s (recΔ b s n)) < mu (recΔ b s (delta n)) :=
 by simpa using mu_merge_lt_rec

 § Closing `mu_lt_eq_diff` 
/-!
Strategy:  Use the same principal‑segment gymnastics on

```
μ(integrate (merge a b)) = ω^4·(μ(merge a b)+1)+1
μ(eqW a b)                = ω^(μ a + μ b + 9)+1
 ```

 1.  Bound the parenthesised coefficient of the left‐hand side below
     `ω^(μ a + μ b + 5)` (reuse `payload_bound_merge_mu`).
 2.  Multiply by `ω^4`; the result sits under
     `ω^(μ a + μ b + 9)` because `4 < μ a + μ b + 9`.
 3.  Add the final `+1` and conclude.
 -/
 lemma mu_lt_eq_diff (a b : Trace) :
   mu (integrate (merge a b)) < mu (eqW a b) := by
    abbreviations
   set C : Ordinal := mu a + mu b with hC
   set B : Ordinal := omega0 ^ (C + 9) with hB
   /- 1 ▸  inner merge bound:  ω^3… + ω^2… ≤ ω^(μ a + 5)  -/
   have h_inner :
       mu (merge a b) + 1 < omega0 ^ (C + 5) := by
     have hpayload := payload_bound_merge_mu a
                         μ(merge a b) + 1 ≤ …   ⇒   strict < by lt_add_one
     have : mu (merge a b) + 1 ≤ omega0 ^ (mu a + 5) := by
       simpa [hC] using hpayload
     exact lt_of_le_of_lt this (lt_add_of_pos_right _ (succ_pos _))
   /- 2 ▸  multiply by ω^4  -/
   have h_mul : omega0 ^ (4 : Ordinal) * (mu (merge a b) + 1) <
                omega0 ^ (4 : Ordinal) * omega0 ^ (C + 5) :=
     Ordinal.mul_lt_mul_of_pos_left h_inner (opow_pos _ _)
   have h_opow :
       omega0 ^ (4 : Ordinal) * omega0 ^ (C + 5) =
       omega0 ^ (4 + (C + 5)) := by
     simpa [opow_add] using (opow_add omega0 (4 : Ordinal) (C + 5)).symm
   have h_exp_lt :
       (4 : Ordinal) + (C + 5) < C + 9 := by
     have : (4 : Ordinal) < 9 := by norm_num
     have : C + 4 < C + 9 := add_lt_add_left this _
     simpa [add_comm, add_left_comm, add_assoc] using this
   have h_upper :
       omega0 ^ (4 + (C + 5)) < B := by
     simpa [hB] using opow_lt_opow_right h_exp_lt
   have h_mul' : omega0 ^ (4 : Ordinal) * (mu (merge a b) + 1) < B := by
     simpa [h_opow] using lt_of_lt_of_le h_mul (le_of_lt h_upper)
   /- 3 ▸  add the outer `+1` and compare with `B+1` (= μ(eqW …)) -/
   have h_final :
       omega0 ^ (4 : Ordinal) * (mu (merge a b) + 1) + 1 < B + 1 :=
     add_lt_add_right h_mul' 1
   simpa [mu, hB, hC] using h_final

  sanity check (compiles => goal closed)
  #eval (0 : Nat)


  sanity check (compiles => goal closed)
  #eval (0 : Nat)



 / every single kernel step strictly decreases `μ` -/
 theorem mu_decreases :
   ∀ {a b : Trace}, OperatorKernelO6.Step a b → mu b < mu a := by
   intro a b h
   cases h with
   | @R_int_delta t          => simpa using mu_void_lt_integrate_delta t
   | R_merge_void_left       => simpa using mu_lt_merge_void_left  b
   | R_merge_void_right      => simpa using mu_lt_merge_void_right b
   | R_merge_cancel          => simpa using mu_lt_merge_cancel     b
   | @R_rec_zero _ _         => simpa using mu_lt_rec_zero _ _
   | @R_rec_succ b s n       => exact mu_lt_rec_succ b s n
   | @R_eq_refl a            => simpa using mu_void_lt_eq_refl a
   | @R_eq_diff a b _        => exact mu_lt_eq_diff a b

 def StepRev (R : Trace → Trace → Prop) : Trace → Trace → Prop := fun a b => R b a

  #check @StepRev
                  StepRev : (Trace → Trace → Prop) → Trace → Trace → Prop

 theorem strong_normalization_forward_trace
   (R : Trace → Trace → Prop)
   (hdec : ∀ {a b : Trace}, R a b → mu b < mu a) :
   WellFounded (StepRev R) := by
   have hwf : WellFounded (fun x y : Trace => mu x < mu y) :=
     InvImage.wf (f := mu) (h := Ordinal.lt_wf)
   have hsub : Subrelation (StepRev R) (fun x y : Trace => mu x < mu y) := by
     intro x y h; exact hdec (a := y) (b := x) h
   exact Subrelation.wf hsub hwf

 theorem strong_normalization_backward
   (R : Trace → Trace → Prop)
   (hinc : ∀ {a b : Trace}, R a b → mu a < mu b) :
   WellFounded R := by
   have hwf : WellFounded (fun x y : Trace => mu x < mu y) :=
     InvImage.wf (f := mu) (h := Ordinal.lt_wf)
   have hsub : Subrelation R (fun x y : Trace => mu x < mu y) := by
     intro x y h; exact hinc h
   exact Subrelation.wf hsub hwf

  #check @strong_normalization_forward_trace
  #check @strong_normalization_backward

  (R : Trace → Trace → Prop) →
    (∀ {a b : Trace}, R a b → mu b < mu a) →
    WellFounded (StepRev R)

 def KernelStep : Trace → Trace → Prop := fun a b => OperatorKernelO6.Step a b

 theorem step_strong_normalization : WellFounded (StepRev KernelStep) := by
    WF target via μ:
   refine Subrelation.wf ?hsub (InvImage.wf (f := mu) (h := Ordinal.lt_wf))
    subrelation: every reversed kernel step strictly drops μ
    (StepRev KernelStep x y) ↔ (KernelStep y x)
   intro x y hxy
   have hk : KernelStep y x := hxy
   have hdec : mu x < mu y := mu_decreases hk
   simpa using hdec
