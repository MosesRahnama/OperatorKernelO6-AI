import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Tactic


open Ordinal

-- set_option diagnostics true
-- set_option diagnostics.threshold 100
-- set_option trace.Meta.Tactic.simp.rewrite true
-- set_option trace.Meta.debug true
-- set_option autoImplicit false
-- set_option maxRecDepth 1000
-- set_option trace.linarith true
-- set_option trace.compiler.ir.result true
set_option linter.unnecessarySimpa false
-- set_option pp.explicit true--(only turn on when you suspect hidden implicits)
-- set_option pp.universes true--(rarely needed)
-- set_option trace.M/eta.isDefEq true (use only for a single failing goal)
-- Variation 3: Unfold definitions carefully

/-!  Extra micro-lemmas missing from Mathlibʼs public API. -/

-- 0.  Strict-monotonicity of ω-powers (stand-alone version).
@[simp] theorem opow_lt_opow_right {a b : Ordinal} (h : a < b) :
    omega0 ^ a < omega0 ^ b := by
  simpa using
    ((Ordinal.isNormal_opow (a := omega0) one_lt_omega0).strictMono h)

/--  If `0 < c` then `a ≤ a + c`.  -/
@[simp] theorem le_of_lt_add_of_pos {a c : Ordinal} (hc : (0 : Ordinal) < c) :
    a ≤ a + c := by
  have hc' : (0 : Ordinal) ≤ c := le_of_lt hc
  simpa using (le_add_of_nonneg_right (a := a) hc')

/--  Invert `opow_lt_opow_right`. -/
@[simp] theorem opow_lt_opow_right_iff {a b : Ordinal} :
    (omega0 ^ a < omega0 ^ b) ↔ a < b := by
  constructor
  · intro hlt
    by_contra hnb
    have hle : b ≤ a := le_of_not_gt hnb
    have hpow : omega0 ^ b ≤ omega0 ^ a :=
      opow_le_opow_right (a := omega0) omega0_pos hle
    exact (not_le_of_gt hlt) hpow
  · exact opow_lt_opow_right
