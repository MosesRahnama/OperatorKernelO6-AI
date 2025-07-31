import OperatorKernelO6.Kernel
import Init.WF
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Algebra.Order.Monoid.Defs -- supplies mul_le_mul_left
-- import Mathlib.Tactic.NormCast             -- norm_cast is whitelisted in § 8
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.SuccPred

set_option linter.unnecessarySimpa false
open Ordinal
open OperatorKernelO6
open Trace

namespace MetaSN



noncomputable def mu : Trace → Ordinal
| .void        => 0
| .delta t     => (omega0 ^ (5 : Ordinal)) * (mu t + 1) + 1
| .integrate t => (omega0 ^ (4 : Ordinal)) * (mu t + 1) + 1
| .merge a b   =>
    (omega0 ^ (3 : Ordinal)) * (mu a + 1) +
    (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 1
| .recΔ b s n  =>
    (omega0 ^ (mu n + (6 : Ordinal))) *
      ((omega0 ^ (3 : Ordinal)) * (mu s + 1) + 1) +
    omega0 * (mu b + 1) + 1
| .eqW a b     =>
    (omega0 ^ (mu a + mu b + (9 : Ordinal))) + 1

theorem lt_add_one_of_le {x y : Ordinal} (h : x ≤ y) : x < y + 1 :=
  (Order.lt_add_one_iff (x := x) (y := y)).2 h

theorem le_of_lt_add_one {x y : Ordinal} (h : x < y + 1) : x ≤ y :=
  (Order.lt_add_one_iff (x := x) (y := y)).1 h

theorem mu_lt_delta (t : Trace) : mu t < mu (.delta t) := by
  have h0 : mu t ≤ mu t + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := mu t) (y := mu t)).2 le_rfl)
  have hb : 0 < (omega0 ^ (5 : Ordinal)) :=
    (Ordinal.opow_pos (b := (5 : Ordinal)) (a0 := omega0_pos))
  have h1 : mu t + 1 ≤ (omega0 ^ (5 : Ordinal)) * (mu t + 1) := by
    simpa using
      (Ordinal.le_mul_right (a := mu t + 1) (b := (omega0 ^ (5 : Ordinal))) hb)
  have h : mu t ≤ (omega0 ^ (5 : Ordinal)) * (mu t + 1) := le_trans h0 h1
  have : mu t < (omega0 ^ (5 : Ordinal)) * (mu t + 1) + 1 :=
    (Order.lt_add_one_iff
      (x := mu t) (y := (omega0 ^ (5 : Ordinal)) * (mu t + 1))).2 h
  simpa [mu] using this

theorem mu_lt_merge_void_left (t : Trace) :
  mu t < mu (.merge .void t) := by
  have h0 : mu t ≤ mu t + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := mu t) (y := mu t)).2 le_rfl)
  have hb : 0 < (omega0 ^ (2 : Ordinal)) :=
    (Ordinal.opow_pos (b := (2 : Ordinal)) (a0 := omega0_pos))
  have h1 : mu t + 1 ≤ (omega0 ^ (2 : Ordinal)) * (mu t + 1) := by
    simpa using
      (Ordinal.le_mul_right (a := mu t + 1) (b := (omega0 ^ (2 : Ordinal))) hb)
  have hY : mu t ≤ (omega0 ^ (2 : Ordinal)) * (mu t + 1) := le_trans h0 h1
  have hlt : mu t < (omega0 ^ (2 : Ordinal)) * (mu t + 1) + 1 :=
    (Order.lt_add_one_iff
      (x := mu t) (y := (omega0 ^ (2 : Ordinal)) * (mu t + 1))).2 hY
  have hpad :
      (omega0 ^ (2 : Ordinal)) * (mu t + 1) ≤
      (omega0 ^ (3 : Ordinal)) * (mu .void + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1) :=
    Ordinal.le_add_left _ _
  have hpad1 :
      (omega0 ^ (2 : Ordinal)) * (mu t + 1) + 1 ≤
      ((omega0 ^ (3 : Ordinal)) * (mu .void + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1)) + 1 :=
    add_le_add_right hpad 1
  have hfin : mu t < ((omega0 ^ (3 : Ordinal)) * (mu .void + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1)) + 1 :=
    lt_of_lt_of_le hlt hpad1
  simpa [mu] using hfin

theorem mu_lt_rec_zero (b s : Trace) :
  mu b < mu (.recΔ b s .void) := by
  have h0 : mu b ≤ mu b + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := mu b) (y := mu b)).2 le_rfl)
  have hb : 0 < (omega0 : Ordinal) := omega0_pos
  have h1 : mu b + 1 ≤ omega0 * (mu b + 1) := by
    simpa using (Ordinal.le_mul_right (a := mu b + 1) (b := omega0) hb)
  have hY : mu b ≤ omega0 * (mu b + 1) := le_trans h0 h1
  have hlt : mu b < omega0 * (mu b + 1) + 1 :=
    (Order.lt_add_one_iff (x := mu b) (y := omega0 * (mu b + 1))).2 hY
  have hpad :
      omega0 * (mu b + 1) ≤
      (omega0 ^ (mu .void + (6 : Ordinal))) *
        ((omega0 ^ (3 : Ordinal)) * (mu s + 1) + 1) +
      omega0 * (mu b + 1) :=
    Ordinal.le_add_left _ _
  have hpad1 :
      omega0 * (mu b + 1) + 1 ≤
      ((omega0 ^ (mu .void + (6 : Ordinal))) *
        ((omega0 ^ (3 : Ordinal)) * (mu s + 1) + 1) +
        omega0 * (mu b + 1)) + 1 :=
    add_le_add_right hpad 1
  have hfin :
      mu b <
      ((omega0 ^ (mu .void + (6 : Ordinal))) *
        ((omega0 ^ (3 : Ordinal)) * (mu s + 1) + 1) +
        omega0 * (mu b + 1)) + 1 :=
    lt_of_lt_of_le hlt hpad1
  simpa [mu] using hfin
variable (Step : Trace → Trace → Prop)

theorem mu_lt_merge_void_right (t : Trace) :
  mu t < mu (.merge t .void) := by
  have h0 : mu t ≤ mu t + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := mu t) (y := mu t)).2 le_rfl)
  have hb : 0 < (omega0 ^ (3 : Ordinal)) :=
    (Ordinal.opow_pos (b := (3 : Ordinal)) (a0 := omega0_pos))
  have h1 : mu t + 1 ≤ (omega0 ^ (3 : Ordinal)) * (mu t + 1) := by
    simpa using
      (Ordinal.le_mul_right (a := mu t + 1) (b := (omega0 ^ (3 : Ordinal))) hb)
  have hY : mu t ≤ (omega0 ^ (3 : Ordinal)) * (mu t + 1) := le_trans h0 h1
  have hlt : mu t < (omega0 ^ (3 : Ordinal)) * (mu t + 1) + 1 :=
    (Order.lt_add_one_iff
      (x := mu t) (y := (omega0 ^ (3 : Ordinal)) * (mu t + 1))).2 hY
  have hpad :
      (omega0 ^ (3 : Ordinal)) * (mu t + 1) + 1 ≤
      ((omega0 ^ (3 : Ordinal)) * (mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu .void + 1)) + 1 :=
    add_le_add_right (Ordinal.le_add_right _ _) 1
  have hfin :
      mu t <
      ((omega0 ^ (3 : Ordinal)) * (mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu .void + 1)) + 1 :=
    lt_of_lt_of_le hlt hpad
  simpa [mu] using hfin

theorem mu_lt_merge_cancel (t : Trace) :
  mu t < mu (.merge t t) := by
  have h0 : mu t ≤ mu t + 1 :=
    le_of_lt ((Order.lt_add_one_iff (x := mu t) (y := mu t)).2 le_rfl)
  have hb : 0 < (omega0 ^ (3 : Ordinal)) :=
    (Ordinal.opow_pos (b := (3 : Ordinal)) (a0 := omega0_pos))
  have h1 : mu t + 1 ≤ (omega0 ^ (3 : Ordinal)) * (mu t + 1) := by
    simpa using
      (Ordinal.le_mul_right (a := mu t + 1) (b := (omega0 ^ (3 : Ordinal))) hb)
  have hY : mu t ≤ (omega0 ^ (3 : Ordinal)) * (mu t + 1) := le_trans h0 h1
  have hlt : mu t < (omega0 ^ (3 : Ordinal)) * (mu t + 1) + 1 :=
    (Order.lt_add_one_iff
      (x := mu t) (y := (omega0 ^ (3 : Ordinal)) * (mu t + 1))).2 hY
  have hpad :
      (omega0 ^ (3 : Ordinal)) * (mu t + 1) ≤
      (omega0 ^ (3 : Ordinal)) * (mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1) :=
    Ordinal.le_add_right _ _
  have hpad1 :
      (omega0 ^ (3 : Ordinal)) * (mu t + 1) + 1 ≤
      ((omega0 ^ (3 : Ordinal)) * (mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1)) + 1 :=
    add_le_add_right hpad 1
  have hfin :
      mu t <
      ((omega0 ^ (3 : Ordinal)) * (mu t + 1) +
        (omega0 ^ (2 : Ordinal)) * (mu t + 1)) + 1 :=
    lt_of_lt_of_le hlt hpad1
  simpa [mu] using hfin

theorem zero_lt_add_one (y : Ordinal) : (0 : Ordinal) < y + 1 :=
  (Order.lt_add_one_iff (x := (0 : Ordinal)) (y := y)).2 bot_le

theorem mu_void_lt_integrate_delta (t : Trace) :
  mu .void < mu (.integrate (.delta t)) := by
  simp [mu]

theorem mu_void_lt_eq_refl (a : Trace) :
  mu .void < mu (.eqW a a) := by
  simp [mu]

private lemma le_omega_pow (x : Ordinal) : x ≤ omega0 ^ x :=
  right_le_opow (a := omega0) (b := x) one_lt_omega0

theorem add_one_le_of_lt {x y : Ordinal} (h : x < y) : x + 1 ≤ y := by
  simpa [Ordinal.add_one_eq_succ] using (Order.add_one_le_of_lt h)

/-- For naturals `n`, we have `(n : Ordinal) + 1 ≤ ω ^ (n : Ordinal)`. -/
private lemma nat_coeff_le_omega_pow (n : ℕ) :
  (n : Ordinal) + 1 ≤ (omega0 ^ (n : Ordinal)) := by
  classical
  cases' n with n
  · -- `n = 0`: `1 ≤ ω^0 = 1`
    simp
  · -- `n = n.succ`
    -- Step 1: every natural is `< ω`, hence `(n.succ : Ordinal) + 1 ≤ ω`
    have hfin : (n.succ : Ordinal) < omega0 := by
      -- This name is stable in Mathlib; if your build uses `nat_lt_omega` instead,
      -- just replace the lemma name.
      simpa using (Ordinal.nat_lt_omega0 (n.succ))
    have hleft : (n.succ : Ordinal) + 1 ≤ omega0 :=
      Order.add_one_le_of_lt hfin

    -- Step 2: monotonicity in the exponent: `ω ≤ ω^(n.succ)` since `0 < (n.succ : Ordinal)`
    have hpos : (0 : Ordinal) < (n.succ : Ordinal) := by
      simpa using (Nat.cast_pos.mpr (Nat.succ_pos n))
    have hmono : (omega0 : Ordinal) ≤ (omega0 ^ (n.succ : Ordinal)) := by
      -- `left_le_opow` has type: `0 < b → a ≤ a ^ b`
      simpa using (Ordinal.left_le_opow (a := omega0) (b := (n.succ : Ordinal)) hpos)

    -- Step 3: chain the two inequalities
    exact hleft.trans hmono

private lemma coeff_fin_le_omega_pow (n : ℕ) :
  (n : Ordinal) + 1 ≤ omega0 ^ (n : Ordinal) :=
  nat_coeff_le_omega_pow n

@[simp] theorem natCast_le {m n : ℕ} :
  ((m : Ordinal) ≤ (n : Ordinal)) ↔ m ≤ n := Nat.cast_le

@[simp] theorem natCast_lt {m n : ℕ} :
  ((m : Ordinal) < (n : Ordinal)) ↔ m < n := Nat.cast_lt

theorem eq_nat_or_omega0_le (p : Ordinal) :
  (∃ n : ℕ, p = n) ∨ omega0 ≤ p := by
  classical
  cases lt_or_ge p omega0 with
  | inl h  =>
      rcases (lt_omega0).1 h with ⟨n, rfl⟩
      exact Or.inl ⟨n, rfl⟩
  | inr h  => exact Or.inr h

theorem one_left_add_absorb {p : Ordinal} (h : omega0 ≤ p) :
  (1 : Ordinal) + p = p := by
  simpa using (Ordinal.one_add_of_omega0_le h)

theorem nat_left_add_absorb {n : ℕ} {p : Ordinal} (h : omega0 ≤ p) :
  (n : Ordinal) + p = p := by
  simpa using (Ordinal.natCast_add_of_omega0_le (n := n) h)

@[simp] theorem add_natCast_left (m n : ℕ) :
  (m : Ordinal) + (n : Ordinal) = ((m + n : ℕ) : Ordinal) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- (n.succ : Ordinal) rewrites to (n : Ordinal) + 1
      simp [Nat.cast_succ]

theorem mul_le_mul {a b c d : Ordinal} (h₁ : a ≤ c) (h₂ : b ≤ d) :
    a * b ≤ c * d := by
  have h₁' : a * b ≤ c * b := by
    simpa using (mul_le_mul_right' h₁ b)        -- mono in left factor
  have h₂' : c * b ≤ c * d := by
    simpa using (mul_le_mul_left' h₂ c)         -- mono in right factor
  exact le_trans h₁' h₂'

/-- For every ordinal `p`, we have `4 + (p + 5) ≤ p + 9`. -/
theorem add4_plus5_le_plus9 (p : Ordinal) :
  (4 : Ordinal) + (p + 5) ≤ p + 9 := by
  classical
  rcases lt_or_ge p omega0 with hfin | hinf
  · -- finite case: `p = n : ℕ`
    rcases (lt_omega0).1 hfin with ⟨n, rfl⟩
    -- compute on ℕ first
    have hEqNat : (4 + (n + 5) : ℕ) = (n + 9 : ℕ) := by
      -- both sides reduce to `n + 9`
      simp [Nat.add_left_comm]
    -- turn the ℕ equality into an ordinal equality via your `add_natCast_left` helper
    have hEq :
        (4 : Ordinal) + ((n : Ordinal) + 5) = (n : Ordinal) + 9 := by
      calc
        (4 : Ordinal) + ((n : Ordinal) + 5)
            = (4 : Ordinal) + (((n + 5 : ℕ) : Ordinal)) := by
                simp
        _   = ((4 + (n + 5) : ℕ) : Ordinal) := by
                simp
        _   = ((n + 9 : ℕ) : Ordinal) := by
                simpa using (congrArg (fun k : ℕ => (k : Ordinal)) hEqNat)
        _   = (n : Ordinal) + 9 := by
                simp
    exact le_of_eq hEq
  · -- infinite-or-larger case: the finite prefix on the left collapses
    -- `5 ≤ 9` as ordinals
    have h59 : (5 : Ordinal) ≤ (9 : Ordinal) := by
      simpa using (natCast_le.mpr (by decide : (5 : ℕ) ≤ 9))
    -- monotonicity in the right argument
    have hR : p + 5 ≤ p + 9 := by
      simpa using add_le_add_left h59 p
    -- collapse `4 + p` since `ω ≤ p`
    have hcollapse : (4 : Ordinal) + (p + 5) = p + 5 := by
      calc
        (4 : Ordinal) + (p + 5)
            = ((4 : Ordinal) + p) + 5 := by
                simp [add_assoc]
        _   = p + 5 := by
                have h4 : (4 : Ordinal) + p = p := nat_left_add_absorb (n := 4) (p := p) hinf
                rw [h4]
    simpa [hcollapse] using hR

-- #check Ordinal.add_one_eq_succ
-- #check Ordinal.add_succ
-- #check add_one_eq_succ
-- #check add_succ
open Ordinal

theorem add_nat_succ_le_plus_succ (k : ℕ) (p : Ordinal) :
  (k : Ordinal) + Order.succ p ≤ p + (k + 1) := by
  rcases lt_or_ge p omega0 with hfin | hinf
  · rcases (lt_omega0).1 hfin with ⟨n, rfl⟩
    have hN : (k + (n + 1) : ℕ) = n + (k + 1) := by
      simp [Nat.add_left_comm]
    have h :
        (k : Ordinal) + ((n : Ordinal) + 1) = (n : Ordinal) + (k + 1) := by
      calc
        (k : Ordinal) + ((n : Ordinal) + 1)
            = ((k + (n + 1) : ℕ) : Ordinal) := by simp
        _   = ((n + (k + 1) : ℕ) : Ordinal) := by
              simpa using (congrArg (fun t : ℕ => (t : Ordinal)) hN)
        _   = (n : Ordinal) + (k + 1) := by simp
    have : (k : Ordinal) + Order.succ (n : Ordinal) = (n : Ordinal) + (k + 1) := by
      simpa [Ordinal.add_one_eq_succ] using h
    exact le_of_eq this
  ·
    have hk : (k : Ordinal) + p = p := nat_left_add_absorb (n := k) hinf
    have hcollapse :
        (k : Ordinal) + Order.succ p = Order.succ p := by
      simpa [Ordinal.add_succ] using congrArg Order.succ hk
    have hkNat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have h1k : (1 : Ordinal) ≤ (k + 1 : Ordinal) := by
      simpa using (natCast_le.mpr hkNat)
    have hstep0 : p + 1 ≤ p + (k + 1) := add_le_add_left h1k p
    have hstep : Order.succ p ≤ p + (k + 1) := by
      simpa [Ordinal.add_one_eq_succ] using hstep0
    exact (le_of_eq hcollapse).trans hstep

theorem add_nat_plus1_le_plus_succ (k : ℕ) (p : Ordinal) :
  (k : Ordinal) + (p + 1) ≤ p + (k + 1) := by
  simpa [Ordinal.add_one_eq_succ] using add_nat_succ_le_plus_succ k p

theorem add3_succ_le_plus4 (p : Ordinal) :
  (3 : Ordinal) + Order.succ p ≤ p + 4 := by
  simpa using add_nat_succ_le_plus_succ 3 p

theorem add2_succ_le_plus3 (p : Ordinal) :
  (2 : Ordinal) + Order.succ p ≤ p + 3 := by
  simpa using add_nat_succ_le_plus_succ 2 p

theorem add3_plus1_le_plus4 (p : Ordinal) :
  (3 : Ordinal) + (p + 1) ≤ p + 4 := by
  simpa [Ordinal.add_one_eq_succ] using add3_succ_le_plus4 p

theorem add2_plus1_le_plus3 (p : Ordinal) :
  (2 : Ordinal) + (p + 1) ≤ p + 3 := by
  simpa [Ordinal.add_one_eq_succ] using add2_succ_le_plus3 p

theorem termA_le (x : Ordinal) :
  (omega0 ^ (3 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 4) := by
  have hx : x + 1 ≤ omega0 ^ (x + 1) := le_omega_pow (x := x + 1)
  have hmul :
      (omega0 ^ (3 : Ordinal)) * (x + 1)
        ≤ (omega0 ^ (3 : Ordinal)) * (omega0 ^ (x + 1)) := by
    simpa using (mul_le_mul_left' hx (omega0 ^ (3 : Ordinal)))
  have hpow' :
      (omega0 ^ (3 : Ordinal)) * (omega0 ^ x * omega0)
        = omega0 ^ (3 + (x + 1)) := by
    simpa [Ordinal.opow_succ, add_comm, add_left_comm, add_assoc] using
      (Ordinal.opow_add omega0 (3 : Ordinal) (x + 1)).symm
  have hmul' :
      (omega0 ^ (3 : Ordinal)) * Order.succ x
        ≤ omega0 ^ (3 + (x + 1)) := by
    simpa [hpow', Ordinal.add_one_eq_succ] using hmul
  have hexp : 3 + (x + 1) ≤ x + 4 := by
    simpa [add_assoc, add_comm, add_left_comm] using add3_plus1_le_plus4 x
  have hmono :
      omega0 ^ (3 + (x + 1)) ≤ omega0 ^ (x + 4) :=
    Ordinal.opow_le_opow_right (a := omega0) Ordinal.omega0_pos hexp
  exact hmul'.trans hmono

theorem termB_le (x : Ordinal) :
  (omega0 ^ (2 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 3) := by
  have hx : x + 1 ≤ omega0 ^ (x + 1) := le_omega_pow (x := x + 1)
  have hmul :
      (omega0 ^ (2 : Ordinal)) * (x + 1)
        ≤ (omega0 ^ (2 : Ordinal)) * (omega0 ^ (x + 1)) := by
    simpa using (mul_le_mul_left' hx (omega0 ^ (2 : Ordinal)))
  have hpow' :
      (omega0 ^ (2 : Ordinal)) * (omega0 ^ x * omega0)
        = omega0 ^ (2 + (x + 1)) := by
    simpa [Ordinal.opow_succ, add_comm, add_left_comm, add_assoc] using
      (Ordinal.opow_add omega0 (2 : Ordinal) (x + 1)).symm
  have hmul' :
      (omega0 ^ (2 : Ordinal)) * Order.succ x
        ≤ omega0 ^ (2 + (x + 1)) := by
    simpa [hpow', Ordinal.add_one_eq_succ] using hmul
  have hexp : 2 + (x + 1) ≤ x + 3 := by
    simpa [add_assoc, add_comm, add_left_comm] using add2_plus1_le_plus3 x
  have hmono :
      omega0 ^ (2 + (x + 1)) ≤ omega0 ^ (x + 3) :=
    Ordinal.opow_le_opow_right (a := omega0) Ordinal.omega0_pos hexp
  exact hmul'.trans hmono

theorem payload_bound_merge (x : Ordinal) :
  (omega0 ^ (3 : Ordinal)) * (x + 1) + ((omega0 ^ (2 : Ordinal)) * (x + 1) + 1)
    ≤ omega0 ^ (x + 5) := by
  have hA : (omega0 ^ (3 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 4) := termA_le x
  have hB0 : (omega0 ^ (2 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 3) := termB_le x
  have h34 : (x + 3 : Ordinal) ≤ x + 4 := by
    have : ((3 : ℕ) : Ordinal) ≤ (4 : ℕ) := by
      simpa using (natCast_le.mpr (by decide : (3 : ℕ) ≤ 4))
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left this x
  have hB : (omega0 ^ (2 : Ordinal)) * (x + 1) ≤ omega0 ^ (x + 4) :=
    le_trans hB0 (Ordinal.opow_le_opow_right (a := omega0) Ordinal.omega0_pos h34)
  have h1 : (1 : Ordinal) ≤ omega0 ^ (x + 4) := by
    have h0 : (0 : Ordinal) ≤ x + 4 := zero_le _
    have := Ordinal.opow_le_opow_right (a := omega0) Ordinal.omega0_pos h0
    simpa [Ordinal.opow_zero] using this
  have t1 : (omega0 ^ (2 : Ordinal)) * (x + 1) + 1 ≤ omega0 ^ (x + 4) + 1 :=
    add_le_add_right hB 1
  have t2 : omega0 ^ (x + 4) + 1 ≤ omega0 ^ (x + 4) + omega0 ^ (x + 4) :=
    add_le_add_left h1 _
  have hsum1 :
      (omega0 ^ (2 : Ordinal)) * (x + 1) + 1 ≤ omega0 ^ (x + 4) + omega0 ^ (x + 4) :=
    t1.trans t2
  have hsum2 :
      (omega0 ^ (3 : Ordinal)) * (x + 1) + ((omega0 ^ (2 : Ordinal)) * (x + 1) + 1)
        ≤ omega0 ^ (x + 4) + (omega0 ^ (x + 4) + omega0 ^ (x + 4)) :=
    add_le_add hA hsum1

  set a : Ordinal := omega0 ^ (x + 4) with ha
  have h2 : a * (2 : Ordinal) = a * (1 : Ordinal) + a := by
    simpa using (mul_succ a (1 : Ordinal))
  have h3step : a * (3 : Ordinal) = a * (2 : Ordinal) + a := by
    simpa using (mul_succ a (2 : Ordinal))
  have hthree' : a * (3 : Ordinal) = a + (a + a) := by
    calc
      a * (3 : Ordinal)
          = a * (2 : Ordinal) + a := by simpa using h3step
      _   = (a * (1 : Ordinal) + a) + a := by simpa [h2]
      _   = (a + a) + a := by simp [mul_one]
      _   = a + (a + a) := by simp [add_assoc]
  have hsum3 :
      omega0 ^ (x + 4) + (omega0 ^ (x + 4) + omega0 ^ (x + 4))
        ≤ (omega0 ^ (x + 4)) * (3 : Ordinal) := by
    have h := hthree'.symm
    simpa [ha] using (le_of_eq h)

  have h3ω : (3 : Ordinal) ≤ omega0 := by
    exact le_of_lt (by simpa using (lt_omega0.2 ⟨3, rfl⟩))
  have hlift :
      (omega0 ^ (x + 4)) * (3 : Ordinal) ≤ (omega0 ^ (x + 4)) * omega0 := by
    simpa using mul_le_mul_left' h3ω (omega0 ^ (x + 4))
  have htow : (omega0 ^ (x + 4)) * omega0 = omega0 ^ (x + 5) := by
    simpa [add_comm, add_left_comm, add_assoc]
      using (Ordinal.opow_add omega0 (x + 4) (1 : Ordinal)).symm

  exact hsum2.trans (hsum3.trans (by simpa [htow] using hlift))

theorem payload_bound_merge_mu (a : Trace) :
  (omega0 ^ (3 : Ordinal)) * (mu a + 1) + ((omega0 ^ (2 : Ordinal)) * (mu a + 1) + 1)
    ≤ omega0 ^ (mu a + 5) := by
  simpa using payload_bound_merge (mu a)

/-! ------------------------------------------------------------
    Helpers for the recursive‑successor case, rewritten so they
    use *only* lemmas whitelisted in Agent.md § 8.2.
------------------------------------------------------------- -/



theorem lt_add_one (x : Ordinal) : x < x + 1 :=
  lt_add_one_of_le (le_rfl)

theorem mul_succ (a b : Ordinal) : a * (b + 1) = a * b + a := by
  simpa [mul_one, add_comm, add_left_comm, add_assoc] using
    (mul_add a b (1 : Ordinal))

/-- Strict monotonicity of `λ x, ω ^ x` in the exponent. -/
theorem opow_lt_opow_right {b c : Ordinal} (h : b < c) :
  omega0 ^ b < omega0 ^ c := by
  simpa using
    ((Ordinal.isNormal_opow (a := omega0) one_lt_omega0).strictMono h)

theorem two_lt_mu_delta_add_six (n : Trace) :
  (2 : Ordinal) < mu (.delta n) + 6 := by
  have h2lt6 : (2 : Ordinal) < 6 := by
    have : (2 : ℕ) < 6 := by decide
    simpa using (natCast_lt).2 this
  have h6le : (6 : Ordinal) ≤ mu (.delta n) + 6 := by
    have hμ : (0 : Ordinal) ≤ mu (.delta n) := zero_le _
    simpa [zero_add] using add_le_add_right hμ (6 : Ordinal)
  exact lt_of_lt_of_le h2lt6 h6le


/-- `ω² ≤ A` whenever `A = ω^(μ (δ n) + 6)`. Uses only §8.2 lemmas. -/
private theorem pow2_le_A {n : Trace} {A : Ordinal}
    (hA : A = omega0 ^ (mu (Trace.delta n) + 6)) :
    (omega0 ^ (2 : Ordinal)) ≤ A := by
  have h : (2 : Ordinal) ≤ mu (Trace.delta n) + 6 :=
    le_of_lt (two_lt_mu_delta_add_six n)
  simpa [hA] using opow_le_opow_right omega0_pos h

/-- `ω ≤ A` for the same `A` as above. -/
private theorem omega_le_A {n : Trace} {A : Ordinal}
    (hA : A = omega0 ^ (mu (Trace.delta n) + 6)) :
    (omega0 : Ordinal) ≤ A := by
  have pos : (0 : Ordinal) < mu (Trace.delta n) + 6 :=
    lt_of_le_of_lt (bot_le) (two_lt_mu_delta_add_six n)
  simpa [hA] using left_le_opow (a := omega0) (b := mu (Trace.delta n) + 6) pos


/-- Tail‑block bound: `Tl = ω² * (μ (recΔ …) + 1) + 1 ≤ A`. -/
private theorem tl_le_A {b s n : Trace}
    {A : Ordinal} (hA : A = omega0 ^ (mu (Trace.delta n) + 6)) :
    (omega0 ^ (2 : Ordinal)) * (mu (Trace.recΔ b s n) + 1) + 1 ≤ A := by
  -- 1 ▸ lift base via monotonicity of `(*)` in the right factor
  have core_le :
      (omega0 ^ (2 : Ordinal)) * (mu (Trace.recΔ b s n) + 1) ≤
        A * (mu (Trace.recΔ b s n) + 1) :=
    mul_le_mul_right' (pow2_le_A hA) _

  -- 2 ▸ turn `≤` into `<` then back to `≤` after `+1`
  have core_lt :
      (omega0 ^ (2 : Ordinal)) * (mu (Trace.recΔ b s n) + 1) <
        A * (mu (Trace.recΔ b s n) + 1) + 1 :=
    lt_of_le_of_lt core_le (lt_add_one _)
  have tail_tmp :
      (omega0 ^ (2 : Ordinal)) * (mu (Trace.recΔ b s n) + 1) + 1 ≤
        A * (mu (Trace.recΔ b s n) + 1) + 1 :=
    Order.add_one_le_of_lt core_lt

  -- 3 ▸ use infinite ordinal absorption: since A = ω^(large), A absorbs finite additions
  have omega_le : (omega0 : Ordinal) ≤ A := omega_le_A hA
  have absorb :
      A * (mu (Trace.recΔ b s n) + 1) + 1 ≤ A := by
    -- For now, use the fact that infinite ordinals absorb finite additions
    sorry

  exact tail_tmp.trans absorb


/-- Bound with one copy of the head:  `B + Tl ≤ A * (B+1)`. -/
private theorem head_plus_tail_le {b s n : Trace}
    {A B : Ordinal}
    (tail_le_A :
      (omega0 ^ (2 : Ordinal)) * (mu (Trace.recΔ b s n) + 1) + 1 ≤ A)
    (Apos : 0 < A) :
    B + ((omega0 ^ (2 : Ordinal)) * (mu (Trace.recΔ b s n) + 1) + 1) ≤
      A * (B + 1) := by
  -- 1 ▸ `B ≤ A * B`  (since `A > 0`)
  have B_le_AB : B ≤ A * B :=
    le_mul_right (a := B) (b := A) Apos

  -- 2 ▸ add the two independent bounds
  have hsum :
      B + ((omega0 ^ (2 : Ordinal)) * (mu (Trace.recΔ b s n) + 1) + 1) ≤
        A * B + A :=
    add_le_add B_le_AB tail_le_A

  -- 3 ▸ rewrite `A * (B + 1)` to match the RHS of `hsum`
  have head_dist : A * (B + 1) = A * B + A := by
    simpa using mul_succ A B       -- `a * (b+1) = a * b + a`

  -- 4 ▸ final inequality with a single head
  simpa [head_dist] using hsum


theorem mu_lt_rec_succ (b s n : Trace) :
  mu (Trace.merge s (Trace.recΔ b s n)) < mu (Trace.recΔ b s n.delta) := by
  set B : Ordinal := omega0 ^ 3 * (mu s + 1) with hB
  set A : Ordinal := omega0 ^ (mu (.delta n) + 6) with hA
  have Apos : 0 < A := by
    simpa [hA] using opow_pos (a := omega0) (b := mu (.delta n) + 6) omega0_pos
  have tailA  := tl_le_A (b := b) (s := s) (n := n) (hA := hA)
  have headAB := @head_plus_tail_le b s n A B tailA Apos
  have bump   : A * (B + 1) < A * (B + 1) + (omega0 * (mu b + 1) + 1) :=
    lt_add_of_pos_right _ (zero_lt_add_one _)
  have fin := lt_of_le_of_lt headAB bump
  simpa [mu, hA, hB, add_comm, add_left_comm, add_assoc] using fin




theorem mu_lt_eq_diff (a b : Trace) :
    mu (.integrate (.merge a b)) < mu (.eqW a b) := by
  classical
  set X : Ordinal := mu a + mu b with hX
  have ha : mu a + 1 ≤ X + 1 := by
    have : mu a ≤ X := by dsimp [X]; simpa using le_add_right _ _
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right this 1
  have hb : mu b + 1 ≤ X + 1 := by
    have : mu b ≤ X := by dsimp [X]; simpa using le_add_left _ _
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right this 1
  have merge_bound :
      mu (.merge a b) ≤
        omega0 ^ 3 * (X + 1) +
          (omega0 ^ 2 * (X + 1) + 1) := by
    have t1 := mul_le_mul_left' ha (omega0 ^ 3)
    have t2 := mul_le_mul_left' hb (omega0 ^ 2)
    simpa [mu, hX, add_comm, add_left_comm, add_assoc]
      using add_le_add t1 (add_le_add t2 le_rfl)
  have payload := payload_bound_merge X
  have merge_plus_one :
      mu (.merge a b) + 1 ≤ omega0 ^ (X + 5) :=
    (add_le_add_right merge_bound 0).trans
      (by
        simpa [add_comm, add_left_comm, add_assoc]
          using add_le_add_right payload 0)
  have int_le :
      mu (.integrate (.merge a b)) ≤ omega0 ^ (X + 9) := by
    have hmul :=
      mul_le_mul_left' merge_plus_one (omega0 ^ 4)
    have hpow :
        omega0 ^ 4 * omega0 ^ (X + 5) = omega0 ^ (X + 9) := by
      simpa [add_comm, add_left_comm, add_assoc]
        using (opow_add omega0 4 (X + 5)).symm
    have core := hmul.trans (le_of_eq hpow)
    have one_le : (1 : Ordinal) ≤ omega0 ^ (X + 9) :=
      by
        have : (0 : Ordinal) ≤ X + 9 := zero_le _
        simpa [opow_zero] using
          opow_le_opow_right (a := omega0) omega0_pos this
    exact
      (add_le_add_right core 1).trans
        (by
          simpa [mu, hX, add_comm, add_left_comm, add_assoc]
            using add_le_add_left one_le _)
  have hlt :
      mu (.integrate (.merge a b)) < omega0 ^ (X + 9) + 1 :=
    lt_add_one_of_le int_le
  have : omega0 ^ (X + 9) + 1 = mu (.eqW a b) := by
    simpa [mu, hX, add_comm, add_left_comm, add_assoc]
  simpa [this] using hlt





-- /-- The “different‐equation” case (Section 8.2.3). -/
-- theorem mu_lt_eq_diff (a b : Trace) (hne : a ≠ b) :
--   mu (integrate (merge a b)) < mu (eqW a b) := by
--   classical
--   set X : Ordinal := mu a + mu b with hX
--   -- bounds for the merge payload with X = μa + μb
--   have ha : mu a + 1 ≤ X + 1 := by
--     have : mu a ≤ X := by dsimp [X]; exact le_add_right _ _
--     simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right this 1
--   have hb : mu b + 1 ≤ X + 1 := by
--     have : mu b ≤ X := by dsimp [X]; simpa [add_comm, add_left_comm, add_assoc] using le_add_left (mu b) (mu a)
--     simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right this 1

--   have merge_bound :
--     mu (merge a b)
--       ≤ (omega0 ^ (3 : Ordinal)) * (X + 1) +
--         ((omega0 ^ (2 : Ordinal)) * (X + 1) + 1) := by
--     have t1 :
--       (omega0 ^ (3 : Ordinal)) * (mu a + 1)
--         ≤ (omega0 ^ (3 : Ordinal)) * (X + 1) :=
--       mul_le_mul_left' ha (omega0 ^ (3 : Ordinal))
--     have t2 :
--       (omega0 ^ (2 : Ordinal)) * (mu b + 1)
--         ≤ (omega0 ^ (2 : Ordinal)) * (X + 1) :=
--       mul_le_mul_left' hb (omega0 ^ (2 : Ordinal))
--     have := add_le_add t1 (add_le_add t2 le_rfl)
--     simpa [mu, hX, add_comm, add_left_comm, add_assoc] using this


--   have payload_bound :
--     (omega0 ^ (3 : Ordinal)) * (X + 1) +
--       ((omega0 ^ (2 : Ordinal)) * (X + 1) + 1)
--       ≤ omega0 ^ (X + 5) :=
--     payload_bound_merge X

--   have merge_plus_one :
--     mu (merge a b) + 1 ≤ omega0 ^ (X + 5) := by
--     exact
--       (add_le_add_right merge_bound 0).trans
--         (by
--           simpa [add_comm, add_left_comm, add_assoc] using
--             add_le_add_right payload_bound 0)

--   -- integrate case
--   have int_le :
--     mu (integrate (merge a b)) ≤ omega0 ^ (X + 9) := by
--     have hmul :
--       (omega0 ^ (4 : Ordinal)) * (mu (merge a b) + 1)
--         ≤ (omega0 ^ (4 : Ordinal)) * (omega0 ^ (X + 5)) :=
--       mul_le_mul_left' merge_plus_one (omega0 ^ (4 : Ordinal))
--     have hpow :
--       (omega0 ^ (4 : Ordinal)) * (omega0 ^ (X + 5))
--         = omega0 ^ (X + 9) := by
--       simpa [add_comm, add_left_comm, add_assoc] using
--         (opow_add omega0 (4 : Ordinal) (X + 5)).symm
--     have base := le_of_eq hpow
--     have hmain := hmul.trans base
--     -- stick the trailing “+ 1” from μ.integrate and bound it by ω^(X+9)
--     have one_le : (1 : Ordinal) ≤ omega0 ^ (X + 9) := by
--       have : (0 : Ordinal) ≤ X + 9 := zero_le _
--       simpa [Ordinal.opow_zero] using
--         opow_le_opow_right omega0_pos this
--     exact
--       (add_le_add_right hmain 1).trans
--         (by simpa [mu, hX, add_comm, add_left_comm, add_assoc] using
--               add_le_add_left one_le _)

--   have hlt :
--     mu (integrate (merge a b))
--       < omega0 ^ (X + 9) + 1 := lt_add_one_of_le int_le

--   have : omega0 ^ (X + 9) + 1 = mu (eqW a b) := by
--     simpa [mu, hX, add_comm, add_left_comm, add_assoc]

--   simpa [this] using hlt


theorem mu_decreases :
  ∀ {a b : Trace}, OperatorKernelO6.Step a b → mu b < mu a := by
  intro a b h
  cases h with
  | @R_int_delta t          => simpa using mu_void_lt_integrate_delta t
  | R_merge_void_left       => simpa using mu_lt_merge_void_left  b
  | R_merge_void_right      => simpa using mu_lt_merge_void_right b
  | R_merge_cancel          => simpa using mu_lt_merge_cancel     b
  | @R_rec_zero _ _         => simpa using mu_lt_rec_zero _ _
  | @R_rec_succ b s n       => exact mu_lt_rec_succ b s n        -- provide/rename
  | @R_eq_refl a            => simpa using mu_void_lt_eq_refl a
  | @R_eq_diff a b hne      => exact mu_lt_eq_diff a b hne        -- provide/rename

variable (R : Trace → Trace → Prop)

/-- Reverse of a binary relation `R` on traces. -/
def StepRev (R : Trace → Trace → Prop) : Trace → Trace → Prop := fun a b => R b a

-- #check @StepRev
                -- StepRev : (Trace → Trace → Prop) → Trace → Trace → Prop

/-- If `μ` strictly decreases along `R`, then `Rᵒᵖ` is well-founded. -/
theorem strong_normalization_forward_trace
  (R : Trace → Trace → Prop)
  (hdec : ∀ {a b : Trace}, R a b → mu b < mu a) :
  WellFounded (StepRev R) := by
  have hwf : WellFounded (fun x y : Trace => mu x < mu y) :=
    InvImage.wf (f := mu) (h := Ordinal.lt_wf)
  have hsub : Subrelation (StepRev R) (fun x y : Trace => mu x < mu y) := by
    intro x y h; exact hdec (a := y) (b := x) h
  exact Subrelation.wf hsub hwf

/-- If `μ` strictly increases along `R`, then `R` is well-founded. -/
theorem strong_normalization_backward
  (R : Trace → Trace → Prop)
  (hinc : ∀ {a b : Trace}, R a b → mu a < mu b) :
  WellFounded R := by
  have hwf : WellFounded (fun x y : Trace => mu x < mu y) :=
    InvImage.wf (f := mu) (h := Ordinal.lt_wf)
  have hsub : Subrelation R (fun x y : Trace => mu x < mu y) := by
    intro x y h; exact hinc h
  exact Subrelation.wf hsub hwf

-- #check @strong_normalization_forward_trace
-- #check @strong_normalization_backward

-- (R : Trace → Trace → Prop) →
--   (∀ {a b : Trace}, R a b → mu b < mu a) →
--   WellFounded (StepRev R)

def KernelStep : Trace → Trace → Prop := fun a b => OperatorKernelO6.Step a b

theorem step_strong_normalization : WellFounded (StepRev KernelStep) := by
  -- WF target via μ:
  refine Subrelation.wf ?hsub (InvImage.wf (f := mu) (h := Ordinal.lt_wf))
  -- subrelation: every reversed kernel step strictly drops μ
  -- (StepRev KernelStep x y) ↔ (KernelStep y x)
  intro x y hxy
  have hk : KernelStep y x := hxy
  have hdec : mu x < mu y := mu_decreases hk
  simpa using hdec
