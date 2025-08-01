# Combined Lean files in OperatorMath

## Arithmetic.lean

```lean
import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta

open OperatorKernelO6 Trace

namespace OperatorKernelO6.Meta

def num : Nat → Trace
| 0 => void
| n+1 => delta (num n)

@[simp] def toNat : Trace → Nat
| void => 0
| delta t => toNat t + 1
| integrate t => toNat t
| merge a b => toNat a + toNat b
| recΔ _ _ n => toNat n
| eqW _ _ => 0

@[simp] theorem toNat_num (n : Nat) : toNat (num n) = n := by
  induction n with
  | zero => simp [num, toNat]
  | succ n ih => simp [num, toNat, ih]

def add (a b : Trace) : Trace := num (toNat a + toNat b)
def mul (a b : Trace) : Trace := num (toNat a * toNat b)

@[simp] theorem toNat_add (a b : Trace) : toNat (add a b) = toNat a + toNat b := by
  simp [add, toNat_num]

@[simp] theorem toNat_mul (a b : Trace) : toNat (mul a b) = toNat a * toNat b := by
  simp [mul, toNat_num]

end OperatorKernelO6.Meta

```

## Complement.lean

```lean
import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Confluence

open OperatorKernelO6 Trace

namespace OperatorKernelO6.Meta

-- Complement operation using integration
def complement (t : Trace) : Trace := integrate t

-- Negation is involutive via double integration cancellation
theorem complement_involution (t : Trace) :
  ∃ u, StepStar (complement (complement t)) u ∧ StepStar t u := by
  unfold complement
  cases t with
  | void => 
    use void
    constructor
    · apply stepstar_of_step; apply R_int_delta
    · apply StepStar.refl
  | delta s =>
    use void  
    constructor
    · apply stepstar_of_step; apply R_int_delta
    · sorry -- Need to show delta s reduces somehow
  | integrate s =>
    use s
    constructor  
    · apply stepstar_of_step; apply R_int_delta
    · apply StepStar.refl
  | merge a b =>
    sorry -- Complex case
  | recΔ b s n =>
    sorry -- Complex case  
  | eqW a b =>
    sorry -- Complex case

-- Complement uniqueness via normal forms
theorem complement_unique {t u v : Trace} 
  (h1 : StepStar (complement t) u) (h2 : StepStar (complement t) v)
  (hu : NormalForm u) (hv : NormalForm v) : u = v := by
  -- Use confluence to get common reduct, then use normal form uniqueness
  have ⟨w, hw1, hw2⟩ := confluence h1 h2
  have : u = w := nf_no_stepstar_forward hu hw1  
  have : v = w := nf_no_stepstar_forward hv hw2
  rw [‹u = w›, ‹v = w›]

-- De Morgan laws
theorem demorgan1 (a b : Trace) :
  ∃ c d, StepStar (complement (merge a b)) c ∧
         StepStar (merge (complement a) (complement b)) d ∧
         ∃ e, StepStar c e ∧ StepStar d e := by
  sorry -- Requires detailed case analysis

theorem demorgan2 (a b : Trace) :
  ∃ c d, StepStar (merge (complement a) (complement b)) c ∧
         StepStar (complement (merge a b)) d ∧  
         ∃ e, StepStar c e ∧ StepStar d e := by
  sorry -- Dual of demorgan1

end OperatorKernelO6.Meta

```

## Confluence.lean

```lean
import OperatorKernelO6.Kernel
import Init.WF
import OperatorKernelO6.Meta.Normalize

open OperatorKernelO6 Trace Step
namespace OperatorKernelO6.Meta

def Confluent : Prop :=
  ∀ {a b c}, StepStar a b → StepStar a c → ∃ d, StepStar b d ∧ StepStar c d

theorem global_confluence : Confluent :=
  confluent_via_normalize

end OperatorKernelO6.Meta

```

## Equality.lean

```lean
import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Meta

open OperatorKernelO6 Trace

namespace OperatorKernelO6.Meta

-- Equality predicate using eqW
def eq_trace (a b : Trace) : Trace := eqW a b

-- Equality reflection: if eqW a b reduces to void, then a and b are equal
theorem eq_refl_reduces (a : Trace) : StepStar (eq_trace a a) void := by
  unfold eq_trace
  apply stepstar_of_step
  apply R_eq_refl

-- Inequality witness: if a ≠ b, then eqW a b reduces to integrate (merge a b)
theorem eq_diff_reduces (a b : Trace) : 
  StepStar (eq_trace a b) (integrate (merge a b)) := by
  unfold eq_trace
  apply stepstar_of_step  
  apply R_eq_diff

-- Equality is decidable in normal forms
def eq_decidable (a b : Trace) (ha : NormalForm a) (hb : NormalForm b) : 
  (a = b) ∨ (a ≠ b) := by
  classical
  exact Classical.em (a = b)

-- Equality properties
theorem eq_symm (a b : Trace) :
  ∃ c, StepStar (eq_trace a b) c ∧ StepStar (eq_trace b a) c := by
  cases Classical.em (a = b) with
  | inl h => 
    rw [h]
    use void
    constructor <;> apply eq_refl_reduces
  | inr h =>
    use integrate (merge a b)
    constructor
    · apply eq_diff_reduces
    · rw [merge_comm] at *; apply eq_diff_reduces
  where
    merge_comm : merge a b = merge b a := by sorry -- Needs confluence

theorem eq_trans (a b c : Trace) :
  ∃ d e f, StepStar (eq_trace a b) d ∧ 
           StepStar (eq_trace b c) e ∧
           StepStar (eq_trace a c) f := by
  sorry -- Complex, requires case analysis and confluence

-- Equality substitution in contexts
def subst_context (ctx : Trace → Trace) (a b : Trace) : Trace :=
  integrate (merge (ctx a) (ctx b))

theorem eq_substitution (a b : Trace) (ctx : Trace → Trace) :
  StepStar (eq_trace a b) void → 
  ∃ d, StepStar (subst_context ctx a b) d := by
  sorry -- Requires careful analysis of context structure

end OperatorKernelO6.Meta

```

## FixedPoint.lean

```lean
import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.SN

open OperatorKernelO6 Trace

namespace OperatorKernelO6.Meta

-- Normalization function (placeholder - uses strong normalization)
def normalize (t : Trace) : Trace := by
  -- In a complete implementation, this would reduce t to normal form
  -- For now, we'll use a placeholder that relies on strong normalization
  sorry

-- Equivalence via normalization
def Equiv (x y : Trace) : Prop := normalize x = normalize y

-- Fixed point witness structure
structure FixpointWitness (F : Trace → Trace) where
  ψ     : Trace
  fixed : Equiv ψ (F ψ)

-- Constructor for fixed point witness
theorem mk_fixed {F} {ψ} (h : Equiv ψ (F ψ)) : FixpointWitness F :=
⟨ψ, h⟩

-- Idempotent functions have fixed points
theorem idemp_fixed {F : Trace → Trace}
  (h : ∀ t, Equiv (F t) (F (F t))) :
  FixpointWitness F :=
⟨F Trace.void, by
  have := h Trace.void
  exact this⟩

-- Fixed point theorem for continuous functions (diagonal construction)
theorem diagonal_fixed (F : Trace → Trace) : ∃ ψ, Equiv ψ (F ψ) := by
  -- This is the key theorem for Gödel's diagonal lemma
  let diag := λ x => F (recΔ x x x)  -- Self-application via recΔ
  let ψ := diag (delta void)         -- Apply to some base term
  use ψ
  sorry -- Detailed proof requires careful analysis of recΔ unfolding

-- Fixed point uniqueness under normalization
theorem fixed_unique {F : Trace → Trace} {ψ₁ ψ₂ : Trace}
  (h₁ : Equiv ψ₁ (F ψ₁)) (h₂ : Equiv ψ₂ (F ψ₂))
  (hF : ∀ x y, Equiv x y → Equiv (F x) (F y)) : -- F respects equivalence
  Equiv ψ₁ ψ₂ := by
  sorry -- Follows from confluence and uniqueness of normal forms

end OperatorKernelO6.Meta

```

## Godel.lean

```lean
import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Arithmetic
import OperatorKernelO6.Meta.ProofSystem

open OperatorKernelO6 Trace

namespace OperatorKernelO6.Meta

-- Diagonal function: given a trace, construct its "quotation"
def diagonal (t : Trace) : Trace :=
  recΔ t (quote_step t) t
where
  quote_step (original : Trace) : Trace :=
    merge original original  -- Simple quotation via doubling

-- Self-reference via diagonal
def self_ref (f : Trace → Trace) : Trace :=
  let diag := diagonal (encode_function f)
  f diag
where
  encode_function (func : Trace → Trace) : Trace :=
    integrate (func void)  -- Rough encoding

-- Gödel sentence: "this sentence is not provable"
def godel_sentence : Trace :=
  self_ref (λ x => complement (provable x (numeral 1000)))

-- Fixed point property
theorem godel_fixed_point :
  ∃ g, StepStar godel_sentence g ∧
       StepStar (complement (provable godel_sentence (numeral 1000))) g := by
  sorry -- Diagonal lemma application

-- First incompleteness theorem
theorem first_incompleteness :
  ¬(∃ bound, StepStar (provable godel_sentence bound) void) ∧
  ¬(∃ bound, StepStar (provable (complement godel_sentence) bound) void) := by
  constructor
  · -- If provable, then true, but then not provable - contradiction
    intro ⟨bound, h⟩
    sorry -- Detailed argument using fixed point
  · -- If complement provable, then false, contradiction with consistency
    intro ⟨bound, h⟩
    sorry -- Use consistency theorem

-- Tarski's undefinability
def truth_predicate (formula : Trace) : Trace :=
  eqW formula void  -- "formula is true"

theorem tarski_undefinability :
  ¬(∃ truth_def : Trace → Trace,
    ∀ f, StepStar (truth_def f) void ↔ StepStar f void) := by
  sorry -- Diagonal argument similar to Gödel

-- Löb's theorem
theorem lob_theorem (formula : Trace) :
  (∃ bound, StepStar (provable (merge (provable formula (numeral 100)) formula) bound) void) →
  (∃ bound', StepStar (provable formula bound') void) := by
  sorry -- Requires careful modal logic analysis

-- Second incompleteness theorem (consistency statement)
def consistency_statement : Trace :=
  complement (merge (provable void (numeral 100)) (provable (complement void) (numeral 100)))

theorem second_incompleteness :
  ¬(∃ bound, StepStar (provable consistency_statement bound) void) := by
  sorry -- Follows from first incompleteness and formalization

end OperatorKernelO6.Meta

```

## Meta.lean

```lean
import OperatorKernelO6.Kernel
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.Linarith

open OperatorKernelO6 Trace Step

namespace OperatorKernelO6.Meta

def deltaDepth : Trace → Nat
| void => 0
| delta t => deltaDepth t + 1
| integrate t => deltaDepth t
| merge a b => deltaDepth a + deltaDepth b
| recΔ _ _ n => deltaDepth n
| eqW a b => deltaDepth a + deltaDepth b

def recDepth : Trace → Nat
| void => 0
| delta t => recDepth t + 1
| integrate t => recDepth t
| merge a b => recDepth a + recDepth b
| recΔ b s n => deltaDepth n + recDepth b + recDepth s + 1
| eqW a b => recDepth a + recDepth b

def sz : Trace → Nat
| void => 1
| delta t => sz t + 1
| integrate t => sz t + 1
| merge a b => sz a + sz b + 1
| recΔ b s n => sz b + sz s + sz n + 1
| eqW a b => sz a + sz b + 1

def eqCount : Trace → Nat
| void => 0
| delta t => eqCount t
| integrate t => eqCount t
| merge a b => eqCount a + eqCount b
| recΔ b s n => eqCount b + eqCount s + eqCount n
| eqW a b => eqCount a + eqCount b + 1

def integCount : Trace → Nat
| void => 0
| delta t => integCount t
| integrate t => integCount t + 1
| merge a b => integCount a + integCount b
| recΔ b s n => integCount b + integCount s + integCount n
| eqW a b => integCount a + integCount b

def recCount : Trace → Nat
| void => 0
| delta t => recCount t
| integrate t => recCount t
| merge a b => recCount a + recCount b
| recΔ b s n => recCount b + recCount s + recCount n + 1
| eqW a b => recCount a + recCount b

def measure (t : Trace) : Prod Nat Nat := (recDepth t, sz t)

def lex (a b : Trace) : Prop :=
  Prod.Lex (· < ·) (· < ·) (measure a) (measure b)

def hasStep : Trace → Bool
| integrate (delta _) => true
| merge void _ => true
| merge _ void => true
| merge _ _ => true
| recΔ _ _ void => true
| recΔ _ _ (delta _) => true
| eqW _ _ => true
| _ => false

def tsize : Trace → Trace
| void => void
| delta t => delta (tsize t)
| integrate t => delta (tsize t)
| merge a b => delta (merge (tsize a) (tsize b))
| recΔ b s n => delta (merge (merge (tsize b) (tsize s)) (tsize n))
| eqW a b => delta (merge (tsize a) (tsize b))

def num0 : Trace := void
def num1 : Trace := delta void
def num2 : Trace := delta num1
def num3 : Trace := delta num2

def succ (t : Trace) : Trace := delta t

end OperatorKernelO6.Meta

```

## Normalize.lean

```lean
import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Termination  -- adjust if your SN file lives elsewhere

open Classical
open OperatorKernelO6 Trace Step

namespace OperatorKernelO6.Meta

noncomputable def normalize : Trace → Trace
| t =>
  if h : ∃ u, Step t u then
    let u := Classical.choose h
    have hu : Step t u := Classical.choose_spec h
    normalize u
  else t
termination_by
  normalize t => size t
decreasing_by
  simp_wf
  exact step_size_decrease (Classical.choose_spec h)

theorem to_norm : ∀ t, StepStar t (normalize t)
| t =>
  by
    classical
    by_cases h : ∃ u, Step t u
    ·
      let u := Classical.choose h
      have hu : Step t u := Classical.choose_spec h
      have ih := to_norm u
      simpa [normalize, h, u, hu] using StepStar.tail hu ih
    ·
      simpa [normalize, h] using StepStar.refl t
termination_by
  to_norm t => size t
decreasing_by
  simp_wf
  exact step_size_decrease (Classical.choose_spec h)

theorem norm_nf : ∀ t, NormalForm (normalize t)
| t =>
  by
    classical
    by_cases h : ∃ u, Step t u
    ·
      let u := Classical.choose h
      have hu : Step t u := Classical.choose_spec h
      have ih := norm_nf u
      simpa [normalize, h, u, hu] using ih
    ·
      intro ex
      rcases ex with ⟨u, hu⟩
      have : Step t u := by simpa [normalize, h] using hu
      exact h ⟨u, this⟩
termination_by
  norm_nf t => size t
decreasing_by
  simp_wf
  exact step_size_decrease (Classical.choose_spec h)

theorem nfp {a b n : Trace} (hab : StepStar a b) (han : StepStar a n) (hn : NormalForm n) :
  StepStar b n := by
  revert b
  induction han with
  | refl =>
      intro b hab _; exact hab
  | tail h an han ih =>
      intro b hab hn'
      cases hab with
      | refl => exact False.elim (hn' ⟨_, h⟩)
      | tail h' hbn => exact ih hbn hn'

def Confluent : Prop :=
  ∀ {a b c}, StepStar a b → StepStar a c → ∃ d, StepStar b d ∧ StepStar c d

theorem global_confluence : Confluent := by
  intro a b c hab hac
  let n := normalize a
  have han : StepStar a n := to_norm a
  have hbn : StepStar b n := nfp hab han (norm_nf a)
  have hcn : StepStar c n := nfp hac han (norm_nf a)
  exact ⟨n, hbn, hcn⟩

end OperatorKernelO6.Meta

```

## OrdinalExtras.lean

```lean
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
-- set_option linter.unnecessarySimpa false
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

```

## ProofSystem.lean

```lean
import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Arithmetic
import OperatorKernelO6.Meta.Equality

open OperatorKernelO6 Trace

namespace OperatorKernelO6.Meta

-- Encode proofs as traces
inductive ProofTerm : Type
| axiom : Trace → ProofTerm
| mp : ProofTerm → ProofTerm → ProofTerm  -- Modus ponens
| gen : (Trace → ProofTerm) → ProofTerm   -- Generalization

-- Convert proof terms to traces
def proof_to_trace : ProofTerm → Trace
| ProofTerm.axiom t => t
| ProofTerm.mp p q => merge (proof_to_trace p) (proof_to_trace q)  
| ProofTerm.gen f => integrate (proof_to_trace (f void))  -- Rough encoding

-- Provability predicate using bounded search via recΔ
def provable (formula : Trace) (bound : Trace) : Trace :=
  recΔ void (search_step formula) bound
where
  search_step (f : Trace) : Trace := 
    eqW f void  -- Check if formula equals void (proven)

-- Σ₁ characterization of provability  
theorem provable_sigma1 (formula : Trace) :
  (∃ proof : Trace, ∃ bound : Trace, 
    StepStar (provable formula bound) void) ↔
  (∃ n : Nat, ∃ proof_term : ProofTerm,
    StepStar (proof_to_trace proof_term) formula) := by
  sorry -- Complex encoding/decoding argument

-- Soundness: if provable then true (in some model)
theorem soundness (formula : Trace) :
  (∃ bound, StepStar (provable formula bound) void) →
  formula = void := by  -- void represents "true"
  sorry -- Requires model-theoretic argument

-- Consistency: not both A and ¬A are provable
theorem consistency (formula : Trace) :
  ¬(∃ b₁ b₂, StepStar (provable formula b₁) void ∧ 
              StepStar (provable (complement formula) b₂) void) := by
  sorry -- Follows from soundness and complement properties

-- Reflection principle encoding
def reflection (formula : Trace) : Trace :=
  eqW (provable formula (numeral 100)) formula

end OperatorKernelO6.Meta

```

## Termination.lean

```lean
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
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.SetTheory.Ordinal.Principal   -- ← additive-principal API
import Mathlib.Tactic
-- import Mathlib.Tactic.Alias
import OperatorKernelO6.Meta.OrdinalExtras   -- ← new tiny helper file



set_option linter.unnecessarySimpa false

open Ordinal
open OperatorKernelO6
open Trace

namespace MetaSN

/-!  Σ───  NEW `mu`  (only the `.recΔ` line differs)  ────────────────Σ -/
noncomputable def mu : Trace → Ordinal
| .void        => 0
| .delta t     => (omega0 ^ (5 : Ordinal)) * (mu t + 1) + 1
| .integrate t => (omega0 ^ (4 : Ordinal)) * (mu t + 1) + 1
| .merge a b   =>
    (omega0 ^ (3 : Ordinal)) * (mu a + 1) +
    (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 1
| .recΔ b s n  =>                                         -- ★ changed ★
    omega0 ^ (mu n + mu s + (6 : Ordinal))                -- tower absorbs μ s
  + omega0 * (mu b + 1) + 1
| .eqW a b     =>
    omega0 ^ (mu a + mu b + (9 : Ordinal)) + 1
/-!  Σ───────────────────────────────────────────────────────────────Σ -/


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

/-- Base-case decrease: `recΔ … void`. -/
theorem mu_lt_rec_zero (b s : Trace) :
    mu b < mu (.recΔ b s .void) := by
  --------------------------------------------------------------------
  -- 1  crude bound  μ b ≤ μ b + 1
  --------------------------------------------------------------------
  have h0 : (mu b) ≤ mu b + 1 :=
    le_of_lt (lt_add_one (mu b))

  --------------------------------------------------------------------
  -- 2  inflate to  ω · (μ b + 1)
  --     `le_mul_right : a ≤ b * a`  〈a := μ b + 1, b := ω〉
  --------------------------------------------------------------------
  have h1 : mu b + 1 ≤ omega0 * (mu b + 1) :=
    Ordinal.le_mul_right (a := mu b + 1) (b := omega0) omega0_pos

  have hle : mu b ≤ omega0 * (mu b + 1) :=
    le_trans h0 h1

  --------------------------------------------------------------------
  -- 3  make it *strict* by adding 1 on the right
  --------------------------------------------------------------------
  have hlt : mu b < omega0 * (mu b + 1) + 1 :=
    lt_of_le_of_lt hle (lt_add_of_pos_right _ zero_lt_one)

  --------------------------------------------------------------------
  -- 4  the padded term is literally a summand of  μ(recΔ … void)
  --    because   μ(recΔ b s void) = ω^(μ s+6) + ω·(μ b+1) + 1
  --------------------------------------------------------------------
  have hpad :
      omega0 * (mu b + 1) + 1 ≤
      omega0 ^ (mu s + 6) + omega0 * (mu b + 1) + 1 := by
    --  ω^(μ s+6) is non-negative, so adding it on the left preserves ≤
    have : (0 : Ordinal) ≤ omega0 ^ (mu s + 6) :=
      Ordinal.zero_le _
    have h₂ :
        omega0 * (mu b + 1) ≤
        omega0 ^ (mu s + 6) + omega0 * (mu b + 1) :=
      le_add_of_nonneg_left this
    exact add_le_add_right h₂ 1

  --------------------------------------------------------------------
  -- 5  chain the two inequalities and unfold the new μ
  --------------------------------------------------------------------
  have : mu b <
         omega0 ^ (mu s + 6) + omega0 * (mu b + 1) + 1 :=
    lt_of_lt_of_le hlt hpad

  simpa [mu] using this
 -- unfold RHS once

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




theorem lt_add_one (x : Ordinal) : x < x + 1 :=
  lt_add_one_of_le (le_rfl)

theorem mul_succ (a b : Ordinal) : a * (b + 1) = a * b + a := by
  simpa [mul_one, add_comm, add_left_comm, add_assoc] using
    (mul_add a b (1 : Ordinal))



theorem two_lt_mu_delta_add_six (n : Trace) :
  (2 : Ordinal) < mu (.delta n) + 6 := by
  have h2lt6 : (2 : Ordinal) < 6 := by
    have : (2 : ℕ) < 6 := by decide
    simpa using (natCast_lt).2 this
  have h6le : (6 : Ordinal) ≤ mu (.delta n) + 6 := by
    have hμ : (0 : Ordinal) ≤ mu (.delta n) := zero_le _
    simpa [zero_add] using add_le_add_right hμ (6 : Ordinal)
  exact lt_of_lt_of_le h2lt6 h6le


private theorem pow2_le_A {n : Trace} {A : Ordinal}
    (hA : A = omega0 ^ (mu (Trace.delta n) + 6)) :
    (omega0 ^ (2 : Ordinal)) ≤ A := by
  have h : (2 : Ordinal) ≤ mu (Trace.delta n) + 6 :=
    le_of_lt (two_lt_mu_delta_add_six n)
  simpa [hA] using opow_le_opow_right omega0_pos h

private theorem omega_le_A {n : Trace} {A : Ordinal}
    (hA : A = omega0 ^ (mu (Trace.delta n) + 6)) :
    (omega0 : Ordinal) ≤ A := by
  have pos : (0 : Ordinal) < mu (Trace.delta n) + 6 :=
    lt_of_le_of_lt (bot_le) (two_lt_mu_delta_add_six n)
  simpa [hA] using left_le_opow (a := omega0) (b := mu (Trace.delta n) + 6) pos

--- not used---
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
  rw [head_dist]; exact hsum


/-- **Strict** monotone: `b < c → ω^b < ω^c`. -/
theorem opow_lt_opow_ω {b c : Ordinal} (h : b < c) :
    omega0 ^ b < omega0 ^ c := by
  simpa using
    ((Ordinal.isNormal_opow (a := omega0) one_lt_omega0).strictMono h)

/-- **Weak** monotone: `p ≤ q → ω^p ≤ ω^q`. Needed for `coeff_lt_A`. -/
theorem opow_le_opow_ω {p q : Ordinal} (h : p ≤ q) :
    omega0 ^ p ≤ omega0 ^ q := by
  exact Ordinal.opow_le_opow_right omega0_pos h   -- library lemma

theorem opow_lt_opow_right {b c : Ordinal} (h : b < c) :
   omega0 ^ b < omega0 ^ c := by
  simpa using
   ((Ordinal.isNormal_opow (a := omega0) one_lt_omega0).strictMono h)

theorem three_lt_mu_delta (n : Trace) :
    (3 : Ordinal) < mu (delta n) + 6 := by
  have : (3 : ℕ) < 6 := by decide
  have h₃₆ : (3 : Ordinal) < 6 := by
    simpa using (Nat.cast_lt).2 this
  have hμ : (0 : Ordinal) ≤ mu (delta n) := Ordinal.zero_le _
  have h₆ : (6 : Ordinal) ≤ mu (delta n) + 6 :=
    le_add_of_nonneg_left (a := (6 : Ordinal)) hμ
  exact lt_of_lt_of_le h₃₆ h₆




set_option diagnostics true
set_option diagnostics.threshold 100
set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.debug true
set_option autoImplicit false
set_option maxRecDepth 1000
set_option trace.linarith true
set_option trace.compiler.ir.result true

theorem w3_lt_A (s n : Trace) :
  omega0 ^ (3 : Ordinal) < omega0 ^ (mu (delta n) + mu s + 6) := by
  ------------------------------------------------------------------
  -- 1 ▸  show   3 < μ(δ n) + μ s + 6
  ------------------------------------------------------------------
  have h₁ : (3 : Ordinal) < mu (delta n) + mu s + 6 := by
    -- 1a ▸ 3 < 6
    have h3_lt_6 : (3 : Ordinal) < 6 := by
      simpa using (natCast_lt).2 (by decide : (3 : ℕ) < 6)

    -- 1b ▸ 6 ≤ μ(δ n) + μ s + 6
    have h6_le : (6 : Ordinal) ≤ mu (delta n) + mu s + 6 := by
      -- positivity of the middle block
      have hμ : (0 : Ordinal) ≤ mu (delta n) + mu s := by
        have hδ : (0 : Ordinal) ≤ mu (delta n) := Ordinal.zero_le _
        have hs : (0 : Ordinal) ≤ mu s         := Ordinal.zero_le _
        exact add_nonneg hδ hs
      -- a ≤ b + a  with  a = 6,  b = μ(δ n)+μ s
      have : (6 : Ordinal) ≤ 6 + (mu (delta n) + mu s) :=
        le_add_of_nonneg_right (a := (6 : Ordinal)) hμ
      -- rearrange to ‑-> μ(δ n)+μ s + 6
      simpa [add_comm, add_left_comm, add_assoc] using this

    exact lt_of_lt_of_le h3_lt_6 h6_le

  ------------------------------------------------------------------
  -- 2 ▸  strict-mono of ω-powers
  ------------------------------------------------------------------
  exact opow_lt_opow_right h₁

-- set_option trace.Meta.Tactic.simp true

theorem coeff_lt_A (s n : Trace) :
    mu s + 1 < omega0 ^ (mu (delta n) + mu s + 3) := by
  ------------------------------------------------------------------
  -- 1 ▸  base step   μ s + 1 < μ s + 3
  ------------------------------------------------------------------
  have h₁ : mu s + 1 < mu s + 3 := by
    have h_nat : (1 : Ordinal) < 3 := by
      norm_num        --   1 < 3  on ℕ  →  ordinals
    simpa using (add_lt_add_left h_nat (mu s))

  ------------------------------------------------------------------
  -- 2 ▸  padding   μ s + 3 ≤ μ (δ n) + μ s + 3
  ------------------------------------------------------------------
  have h₂ : mu s + 3 ≤ mu (delta n) + mu s + 3 := by
    -- since `0 ≤ μ(δ n)` we can insert that non-neg term on the left
    have hμ : (0 : Ordinal) ≤ mu (delta n) := Ordinal.zero_le _
    have h_le : (mu s) ≤ mu (delta n) + mu s :=
      (le_add_of_nonneg_left (a := mu s) hμ)
    -- add `3` on the right (left-mono in ordinal addition)
    simpa [add_comm, add_left_comm, add_assoc]
      using add_le_add_right h_le 3

  ------------------------------------------------------------------
  -- 3 ▸  chaining   μ s + 1 < μ (δ n) + μ s + 3
  ------------------------------------------------------------------
  have h_chain : mu s + 1 < mu (delta n) + mu s + 3 :=
    lt_of_lt_of_le h₁ h₂

  ------------------------------------------------------------------
  -- 4 ▸  final leap   x ≤ ω^x
  ------------------------------------------------------------------
  have h_big : mu (delta n) + mu s + 3 ≤
               omega0 ^ (mu (delta n) + mu s + 3) :=
    le_omega_pow (x := mu (delta n) + mu s + 3)

  exact lt_of_lt_of_le h_chain h_big


theorem head_lt_A (s n : Trace) :
  let A : Ordinal := omega0 ^ (mu (delta n) + mu s + 6);
  omega0 ^ (3 : Ordinal) * (mu s + 1) < A := by
  intro A
  ------------------------------------------------------------------
  -- 1 ▸  head payload ≤ ω^(μ s+4)
  ------------------------------------------------------------------
  have h₁ : omega0 ^ (3 : Ordinal) * (mu s + 1) ≤
            omega0 ^ (mu s + 4) :=
    termA_le (x := mu s)

  ------------------------------------------------------------------
  -- 2 ▸  exponent inequality   μ s+4 < μ δ n + μ s + 6
  ------------------------------------------------------------------
  -- 2a  finite padding on the left
  have h_left : mu s + 4 < mu s + 6 := by
    have : (4 : Ordinal) < 6 := by
      simpa using (natCast_lt).2 (by decide : (4 : ℕ) < 6)
    simpa using (add_lt_add_left this (mu s))

  -- 2b  insert `μ δ n` on the left using monotonicity
  have h_pad : mu s + 6 ≤ mu (delta n) + mu s + 6 := by
    -- 0 ≤ μ δ n
    have hμ : (0 : Ordinal) ≤ mu (delta n) := Ordinal.zero_le _
    -- μ s ≤ μ δ n + μ s
    have h₀ : (mu s) ≤ mu (delta n) + mu s :=
      le_add_of_nonneg_left hμ
    -- add the finite 6 to both sides
    have h₀' : mu s + 6 ≤ (mu (delta n) + mu s) + 6 :=
      add_le_add_right h₀ 6
    simpa [add_comm, add_left_comm, add_assoc] using h₀'

  -- 2c  combine
  have h_exp : mu s + 4 < mu (delta n) + mu s + 6 :=
    lt_of_lt_of_le h_left h_pad

  ------------------------------------------------------------------
  -- 3 ▸  lift through ω^(·)
  ------------------------------------------------------------------
  have h₂ : omega0 ^ (mu s + 4) <
            omega0 ^ (mu (delta n) + mu s + 6) :=
    opow_lt_opow_right h_exp

  ------------------------------------------------------------------
  -- 4 ▸  chain the two bounds
  ------------------------------------------------------------------
  have h_final :
      omega0 ^ (3 : Ordinal) * (mu s + 1) <
      omega0 ^ (mu (delta n) + mu s + 6) :=
    lt_of_le_of_lt h₁ h₂

  ------------------------------------------------------------------
  -- 5 ▸  rewrite target `A`
  ------------------------------------------------------------------
  simpa [A] using h_final


private lemma two_lt_three : (2 : Ordinal) < 3 := by
  have : (2 : ℕ) < 3 := by decide
  simpa using (Nat.cast_lt).2 this



@[simp] theorem opow_mul_lt_of_exp_lt
    {β α γ : Ordinal} (hβ : β < α) (hγ : γ < omega0) :
    omega0 ^ β * γ < omega0 ^ α := by
  ------------------------------------------------------------------
  -- 1 ▸  ω^β·γ < ω^β·ω        (absorb the finite multiplier)
  ------------------------------------------------------------------
  have hpos : (0 : Ordinal) < omega0 ^ β :=
    Ordinal.opow_pos (a := omega0) (b := β) omega0_pos
  have h₁ : omega0 ^ β * γ < omega0 ^ β * omega0 :=
    Ordinal.mul_lt_mul_of_pos_left hγ hpos

  ------------------------------------------------------------------
  -- 2 ▸  rewrite  ω^β·ω  as  ω^(β+1)    (disable `opow_succ` to stop loops)
  ------------------------------------------------------------------
  have h_eq : omega0 ^ β * omega0 = omega0 ^ (β + 1) := by
    simpa [opow_add] using (opow_add omega0 β 1).symm
  have h₁' : omega0 ^ β * γ < omega0 ^ (β + 1) := by
    simpa [h_eq, -opow_succ] using h₁

  ------------------------------------------------------------------
  -- 3 ▸  monotone-but-weak   β+1 ≤ α  ⇒  ω^(β+1) ≤ ω^α
  ------------------------------------------------------------------
  have h_exp : β + 1 ≤ α := Order.add_one_le_of_lt hβ  -- FIXED: Use Order.add_one_le_of_lt instead
  have h₂ : omega0 ^ (β + 1) ≤ omega0 ^ α :=
    opow_le_opow_right (a := omega0) omega0_pos h_exp

  ------------------------------------------------------------------
  -- 4 ▸  chain  (strict < then weak ≤ gives strict <)
  ------------------------------------------------------------------
  exact lt_of_lt_of_le h₁' h₂







lemma omega_pow_add_lt
    {κ α β : Ordinal} (hκ : 0 < κ)
    (hα : α < omega0 ^ κ) (hβ : β < omega0 ^ κ) :
    α + β < omega0 ^ κ := by
  have _ : 0 < κ := hκ
  have hprin : Principal (fun x y : Ordinal => x + y) (omega0 ^ κ) :=
    Ordinal.principal_add_omega0_opow κ
  exact hprin hα hβ



lemma omega_pow_add3_lt
    {κ α β γ : Ordinal} (hκ : 0 < κ)
    (hα : α < omega0 ^ κ) (hβ : β < omega0 ^ κ) (hγ : γ < omega0 ^ κ) :
    α + β + γ < omega0 ^ κ := by
  have hsum : α + β < omega0 ^ κ :=
    omega_pow_add_lt hκ hα hβ
  have hsum' : α + β + γ < omega0 ^ κ :=
    omega_pow_add_lt hκ (by simpa using hsum) hγ
  simpa [add_assoc] using hsum'

-- Register in the toolkit (one‑liners appended manually).


@[simp] lemma add_one_lt_omega0 (k : ℕ) :
    ((k : Ordinal) + 1) < omega0 := by
  -- `k.succ < ω`
  have : ((k.succ : ℕ) : Ordinal) < omega0 := by
    simpa using (nat_lt_omega0 k.succ)
  simpa [Nat.cast_succ, add_comm, add_left_comm, add_assoc,
         add_one_eq_succ] using this

@[simp] lemma one_le_omega0 : (1 : Ordinal) ≤ omega0 :=
  (le_of_lt (by
    have : ((1 : ℕ) : Ordinal) < omega0 := by
      simpa using (nat_lt_omega0 1)
    simpa using this))




lemma add_le_add_of_le_of_nonneg {a b c : Ordinal}
    (h : a ≤ b) (_ : (0 : Ordinal) ≤ c := by exact Ordinal.zero_le _)
    : a + c ≤ b + c :=
  add_le_add_right h c

@[simp] lemma lt_succ (a : Ordinal) : a < Order.succ a := by
  have : a < a + 1 := lt_add_of_pos_right _ zero_lt_one
  simpa [Order.succ] using this

alias le_of_not_gt := le_of_not_lt

attribute [simp] Ordinal.IsNormal.strictMono



-- Variation 3: Unfold definitions carefully
@[simp] lemma succ_succ (a : Ordinal) :
    Order.succ (Order.succ a) = a + 2 := by
  have h1 : Order.succ a = a + 1 := rfl
  rw [h1]
  have h2 : Order.succ (a + 1) = (a + 1) + 1 := rfl
  rw [h2, add_assoc]
  norm_num

/-- converse rewrite; handy when the RHS shows up first -/
lemma add_two (a : Ordinal) :
    a + 2 = Order.succ (Order.succ a) := (succ_succ a).symm



set_option diagnostics true
set_option diagnostics.threshold 100
set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.debug true
set_option autoImplicit false
set_option maxRecDepth 1000
set_option trace.linarith true
set_option trace.compiler.ir.result true
-- set_option pp.explicit true (only turn on when you suspect hidden implicits)
-- set_option pp.universes true (rarely needed)
-- set_option trace.Meta.isDefEq true (use only for a single failing goal)
-- Variation 3: Unfold definitions carefully

/--  `a ≤ a + c` whenever `0 ≤ c` (in particular for `0 < c`). -/
@[simp] theorem le_self_add {a c : Ordinal} (hc : (0 : Ordinal) ≤ c) :
    a ≤ a + c := by
  simpa using le_add_of_nonneg_right hc


/--
Invert the strict-monotone ω-power:
`ω ^ a < ω ^ b` iff `a < b`.
(The forward half is `opow_lt_opow_ω`; we supply the converse.)
-/
@[simp] theorem opow_lt_opow_right_iff {a b : Ordinal} :
    (omega0 ^ a < omega0 ^ b) ↔ a < b := by
  constructor
  · intro hlt
    by_contra hnb          -- assume ¬ a < b, hence b ≤ a
    have hle : b ≤ a := le_of_not_gt hnb
    have hle' : omega0 ^ b ≤ omega0 ^ a := opow_le_opow_ω hle
    exact (not_le_of_gt hlt) hle'
  · intro hlt
    exact opow_lt_opow_ω hlt


lemma tail_lt_A {b s n : Trace} :
    let A : Ordinal := omega0 ^ (mu (delta n) + mu s + 6)
    omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) < A := by
  intro A

  ------------------------------------------------------------------
  -- Step 1.  `tail ≤ ω^(μ(rec)+3)`
  ------------------------------------------------------------------
  have h_coeff :
      omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) ≤
      omega0 ^ (mu (recΔ b s n) + 3) :=
    termB_le (x := mu (recΔ b s n))

  ------------------------------------------------------------------
  -- Step 2.  Show   μ(rec) + 3 < μ(δ n) + μ s + 6
  --         via  ω-powers and strict monotonicity
  ------------------------------------------------------------------
  -- 2a.  First prove `ω ^ μ(rec) < A`.
  have hpow_left :
      omega0 ^ (mu (recΔ b s n)) < A := by
    --   μ(rec)  < μ(rec)+1
    have hlt : mu (recΔ b s n) < mu (recΔ b s n) + 1 :=
      lt_add_one _
    --   ω^μ(rec) < ω^(μ(rec)+1)
    have hpow := (isNormal_opow one_lt_omega0).strictMono hlt
    --   need  ω^(μ(rec)+1) < A;  use principal-segment property of A
    have hμ1_lt : (mu (recΔ b s n) + 1) < A := by
      -- A is additive-principal ⇒ x< A ∧ y< A ⇒ x+y < A.
      have hprin : Principal (fun x y : Ordinal => x + y) A :=
        principal_add_omega0_opow (mu (delta n) + mu s + 6)
      --   tower < A (strict because δ n bumps exponent)
      have htower : omega0 ^ (mu n + mu s + 6) < A := by
        have h_exp : (mu n + mu s + 6) < (mu (delta n) + mu s + 6) := by
          have := mu_lt_delta n
          simpa [add_comm, add_left_comm, add_assoc] using
            add_lt_add_left this (mu s + 6)
        exact opow_lt_opow_right h_exp
      --   rest < ω² < A   (simple bound)
      have hrest : omega0 * (mu b + 1) + 2 < omega0 ^ (2 : Ordinal) := by
        have h0 : (mu b) < omega0 := (nat_lt_omega0 _).trans_le
          (Ordinal.le_of_lt_add_of_pos (zero_lt_two))
        have : omega0 * (mu b + 1) < omega0 * omega0 :=
          Ordinal.mul_lt_mul_of_pos_left (add_lt_add_right h0 1) omega0_pos
        have h2 : (2 : Ordinal) < omega0 := nat_lt_omega0 _
        have : omega0 * (mu b + 1) + 2 < omega0 * omega0 + omega0 :=
          add_lt_add_of_lt_of_lt this h2
        simpa [mul_comm] using
          (add_lt_add_left (lt_of_lt_of_le this (add_le_add_right
              (le_of_eq (add_omega0_left _).symm) _)) _)
      -- combine via principal segment
      have hμ1 : mu (recΔ b s n) + 1 =
          omega0 ^ (mu n + mu s + 6) + (omega0 * (mu b + 1) + 2) := by
        simp [mu]
      have : (omega0 ^ (mu n + mu s + 6)) <
          A := htower
      have : (omega0 * (mu b + 1) + 2) < A := lt_trans hrest
        (show omega0 ^ (2 : Ordinal) < A from
          opow_lt_opow_right
            (by
              have : (2 : Ordinal) < mu (delta n) + mu s + 6 := by
                have := (by norm_num : (2 : Ordinal) < 6)
                exact this.trans_le (by
                  have : (0 : Ordinal) ≤ _ := by
                    exact (Ordinal.add_nonneg (Ordinal.zero_le _) (Ordinal.zero_le _))
                  simpa using le_add_of_nonneg_left this)
              exact this))
      have := hprin this (lt_of_le_of_lt (le_of_eq hμ1) this)
      simpa [hμ1] using this
    exact lt_of_lt_of_le hpow hμ1_lt

  -- 2b.  Strict-mono ⇒ inequality on exponents.
  have hgap :
      mu (recΔ b s n) + 3 < mu (delta n) + mu s + 6 := by
    have hmono := (opow_lt_opow_right_iff)
    --  ω^(μ(rec)+3) < A  because  ω^(μ(rec)) < A  and multiplying by ω³.
    have hpow_lt : omega0 ^ (mu (recΔ b s n) + 3) < A := by
      have : omega0 ^ (mu (recΔ b s n) + 3) =
          omega0 ^ (mu (recΔ b s n)) * omega0 ^ (3 : Ordinal) := by
        simpa [opow_add] using (opow_add _ _ _).symm
      have := Ordinal.mul_lt_mul_of_pos_right hpow_left
        (opow_pos _ _)
      simpa [this] using this
    have := hmono.1 hpow_lt
    -- subtract 3 on both sides
    have : mu (recΔ b s n) + 3 < mu (delta n) + mu s + 6 :=
      (add_lt_add_iff_right _).1 this
    simpa using this

  ------------------------------------------------------------------
  -- Step 3.  Now chain inequalities:
  ------------------------------------------------------------------
  have hpow_lt_tail :
      omega0 ^ (mu (recΔ b s n) + 3) < A :=
    opow_lt_opow_right hgap
  exact lt_of_le_of_lt h_coeff hpow_lt_tail


-- -- § Finishing `mu_merge_lt_rec` --------------------------------
lemma mu_merge_lt_rec {b s n : Trace} :
  mu (merge s (recΔ b s n)) < mu (recΔ b s (delta n)) := by
  -- rename the dominant tower once and for all
  set A : Ordinal := omega0 ^ (mu (delta n) + mu s + 6) with hA
  -- ❶  head        (ω³ payload)  < A
  have h_head : omega0 ^ (3 : Ordinal) * (mu s + 1) < A := by
    simpa [hA] using head_lt_A s n
  -- ❷  tail        (ω² payload)  < A  (new lemma)
  have h_tail : omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) < A := by
    simpa [hA] using tail_lt_A (b := b) (s := s) (n := n)
  -- ❸  sum of head + tail + 1 < A.
  have h_sum :
      omega0 ^ (3 : Ordinal) * (mu s + 1) +
      (omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) + 1) < A := by
    -- First fold inner `tail+1` under A.
    have h_tail1 :
        omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) + 1 < A :=
      omega_pow_add_lt (by norm_num) h_tail (by
        -- `1 < A` trivially (tower is non‑zero)
        have : (1 : Ordinal) < A := by
          have : (0 : Ordinal) < A := opow_pos _ _ omega0_pos
          exact lt_of_le_of_lt (one_le_of_lt this) this
        exact this)
    -- Then fold head + (tail+1).
    simpa [add_assoc] using
      omega_pow_add_lt (by norm_num) h_head (by
        have := h_tail1; simpa [add_comm] using this)
  -- ❹  RHS is   A + ω·… + 1  >  A  >  LHS.
  have h_rhs_gt_A : A < mu (recΔ b s (delta n)) := by
    -- by definition of μ(recΔ … (δ n)) (see new μ)
    have : A < A + omega0 * (mu b + 1) + 1 := by
      have hpos : (0 : Ordinal) < omega0 * (mu b + 1) + 1 := by
        have := le_add_of_nonneg_left (omega0 * (mu b + 1)) (le_of_lt (succ_pos 0))
        exact lt_of_lt_of_le (zero_lt_one) this
      simpa [mu, hA] using lt_add_of_pos_right A hpos
    simpa [mu, hA] using this
  -- ❺  chain inequalities.
  have : mu (merge s (recΔ b s n)) < A := by
    -- rewrite μ(merge …) exactly and apply `h_sum`
    have : mu (merge s (recΔ b s n)) =
        omega0 ^ (3 : Ordinal) * (mu s + 1) +
        (omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) + 1) := by
      simp [mu]
    simpa [this] using h_sum
  exact lt_trans this h_rhs_gt_A

@[simp] lemma mu_lt_rec_succ (b s n : Trace) :
  mu (merge s (recΔ b s n)) < mu (recΔ b s (delta n)) :=
by simpa using mu_merge_lt_rec

lemma mu_lt_eq_diff (a b : Trace) :
  mu (integrate (merge a b)) < mu (eqW a b) := by
  -- abbreviations
  set C : Ordinal := mu a + mu b with hC
  set B : Ordinal := omega0 ^ (C + 9) with hB
  /- 1 ▸  inner merge bound:  ω^3… + ω^2… ≤ ω^(μ a + 5)  -/
  have h_inner :
      mu (merge a b) + 1 < omega0 ^ (C + 5) := by
    have hpayload := payload_bound_merge_mu a
    --                    μ(merge a b) + 1 ≤ …   ⇒   strict < by lt_add_one
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

def KernelStep : Trace → Trace → Prop := fun a b => OperatorKernelO6.Step a b

theorem step_strong_normalization : WellFounded (StepRev KernelStep) := by
  refine Subrelation.wf ?hsub (InvImage.wf (f := mu) (h := Ordinal.lt_wf))
  intro x y hxy
  have hk : KernelStep y x := hxy
  have hdec : mu x < mu y := mu_decreases hk
  simpa using hdec

```

