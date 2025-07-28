-- OperatorKernelO6/Meta/Termination.lean
-- META LAYER: Can use Nat, Ordinals, and any Lean features

import OperatorKernelO6.Kernel
import Mathlib.SetTheory.Ordinal.Arithmetic

namespace OperatorKernelO6.Meta

open OperatorKernelO6 Trace

-- ═══════════════════════════════════════════════════════════════
-- MEASURE FUNCTIONS (Meta level - uses Nat)
-- ═══════════════════════════════════════════════════════════════

-- Count δ-height in recΔ arguments
def recDepth : Trace → Nat
| void => 0
| delta t => recDepth t
| integrate t => recDepth t
| merge t₁ t₂ => max (recDepth t₁) (recDepth t₂)
| recΔ b s void => 0
| recΔ b s (delta n) => 1 + recDepth n  -- KEY: counts δ-nesting
| recΔ b s t => recDepth t
| eqW t₁ t₂ => max (recDepth t₁) (recDepth t₂)

-- Total size of trace
def traceSize : Trace → Nat
| void => 1
| delta t => 1 + traceSize t
| integrate t => 1 + traceSize t
| merge t₁ t₂ => 1 + traceSize t₁ + traceSize t₂
| recΔ b s t => 1 + traceSize b + traceSize s + traceSize t
| eqW t₁ t₂ => 1 + traceSize t₁ + traceSize t₂

-- ═══════════════════════════════════════════════════════════════
-- ORDINAL MEASURE
-- ═══════════════════════════════════════════════════════════════

open Ordinal

-- The key measure: ω^(recDepth) + size
def ordinalMeasure (t : Trace) : Ordinal :=
  ω ^ (recDepth t : Ordinal) + (traceSize t : Ordinal)

-- ═══════════════════════════════════════════════════════════════
-- MEASURE DECREASE PROOFS
-- ═══════════════════════════════════════════════════════════════

-- Helper: size of merge is bigger than its parts
lemma merge_size_increase (s t : Trace) : 
  traceSize s < traceSize (merge s t) ∧ traceSize t < traceSize (merge s t) := by
  simp [traceSize]
  constructor <;> omega

-- Helper: ω^n dominates any finite number
lemma omega_pow_dominates (n : Nat) (k : Nat) : 
  (k : Ordinal) < ω ^ (n + 1 : Ordinal) := by
  rw [pow_succ]
  exact lt_of_lt_of_le (Ordinal.nat_lt_omega k) (le_mul_of_one_le_right (Ordinal.zero_lt_omega) (one_le_pow_iff.mpr ⟨n, rfl⟩))

-- Main theorem: each step decreases the ordinal measure
theorem step_decreases_ordinal {a b : Trace} (h : Step a b) : 
  ordinalMeasure b < ordinalMeasure a := by
  cases h with
  
  -- R_int_delta: integrate (delta t) → void
  | R_int_delta t =>
    simp [ordinalMeasure, recDepth, traceSize]
    exact add_lt_add_left (Ordinal.nat_cast_lt.mpr (by omega : 1 < 2 + traceSize t)) _
  
  -- R_merge_void_left: merge void t → t
  | R_merge_void_left t =>
    simp [ordinalMeasure, recDepth, traceSize]
    exact add_lt_add_left (Ordinal.nat_cast_lt.mpr (by omega : traceSize t < 2 + traceSize t)) _
  
  -- R_merge_void_right: merge t void → t  
  | R_merge_void_right t =>
    simp [ordinalMeasure, recDepth, traceSize]
    exact add_lt_add_left (Ordinal.nat_cast_lt.mpr (by omega : traceSize t < 2 + traceSize t)) _
  
  -- R_merge_cancel: merge t t → t
  | R_merge_cancel t =>
    simp [ordinalMeasure, recDepth, traceSize]
    exact add_lt_add_left (Ordinal.nat_cast_lt.mpr (by omega : traceSize t < 1 + traceSize t + traceSize t)) _
  
  -- R_rec_zero: recΔ b s void → b
  | R_rec_zero b s =>
    simp [ordinalMeasure, recDepth, traceSize]
    exact add_lt_add_left (Ordinal.nat_cast_lt.mpr (by omega : traceSize b < 2 + traceSize b + traceSize s)) _
  
  -- R_rec_succ: recΔ b s (delta n) → merge s (recΔ b s n)
  -- THIS IS THE KEY CASE!
  | R_rec_succ b s n =>
    simp [ordinalMeasure, recDepth, traceSize]
    -- LHS: ω^(1 + recDepth n) + (1 + size b + size s + (1 + size n))
    -- RHS: ω^(recDepth n) + (1 + size s + (1 + size b + size s + size n))
    -- Need to show RHS < LHS
    -- Key: ω^(k+1) = ω * ω^k > ω^k + any finite number
    have h1 : recDepth (merge s (recΔ b s n)) = recDepth n := by
      simp [recDepth]
    have h2 : ω ^ (recDepth n : Ordinal) < ω ^ (1 + recDepth n : Ordinal) := by
      rw [pow_succ]
      nth_rewrite 2 [← one_mul (ω ^ (recDepth n : Ordinal))]
      exact mul_lt_mul_of_pos_right one_lt_omega (pow_pos omega_pos _)
    -- Even though size increases, the ω^k decrease dominates
    calc ordinalMeasure (merge s (recΔ b s n))
        = ω ^ (recDepth n : Ordinal) + (traceSize (merge s (recΔ b s n)) : Ordinal) := by rw [h1]; rfl
      _ < ω ^ (1 + recDepth n : Ordinal) + 0 := add_lt_add_of_lt_of_le h2 (Ordinal.zero_le _)
      _ ≤ ω ^ (1 + recDepth n : Ordinal) + (2 + traceSize b + traceSize s + traceSize n : Ordinal) := 
          add_le_add_left (Ordinal.nat_cast_le.mpr (by omega : 0 ≤ 2 + traceSize b + traceSize s + traceSize n)) _
      _ = ordinalMeasure (recΔ b s (delta n)) := by simp [ordinalMeasure, recDepth, traceSize]
  
  -- R_eq_refl: eqW a a → void
  | R_eq_refl a =>
    simp [ordinalMeasure, recDepth, traceSize]
    exact add_lt_add_left (Ordinal.nat_cast_lt.mpr (by omega : 1 < 1 + traceSize a + traceSize a)) _
  
  -- R_eq_diff: eqW a b → integrate (merge a b)
  | R_eq_diff a b =>
    simp [ordinalMeasure, recDepth, traceSize]
    -- Size: 1 + size a + size b → 1 + (1 + size a + size b) 
    -- But recDepth stays same or decreases
    exact add_lt_add_left (Ordinal.nat_cast_lt.mpr (by omega : 2 + traceSize a + traceSize b < 1 + traceSize a + traceSize b)) _

-- ═══════════════════════════════════════════════════════════════
-- STRONG NORMALIZATION THEOREM
-- ═══════════════════════════════════════════════════════════════

-- Well-foundedness of the measure
theorem ordinal_measure_wf : WellFounded (fun a b => ordinalMeasure a < ordinalMeasure b) :=
  InvImage.wf ordinalMeasure (Ordinal.wf)

-- Accessibility follows from well-foundedness
theorem strong_normalization : ∀ t : Trace, Acc Step t := by
  intro t
  apply Acc.intro
  intro b h
  -- Use the fact that ordinalMeasure decreases
  have : ordinalMeasure b < ordinalMeasure t := step_decreases_ordinal h
  -- Apply well-founded induction
  exact Acc.inv (WellFounded.apply ordinal_measure_wf t) this

-- Export theorem without ordinals
theorem all_traces_normalize : ∀ t : Trace, ∃ n : Trace, StepStar t n ∧ NormalForm n := by
  intro t
  -- Use strong normalization to build the proof
  have acc := strong_normalization t
  -- ... (construct normal form using accessibility)
  sorry  -- Complete proof requires showing existence via accessibility

end OperatorKernelO6.Meta