
# Ordinal Toolkit EXT

## 0  Canonical Import Block — _no surprises_

import OperatorKernelO6.Kernel              -- kernel
import Init.WF                               -- Well-Founded, Acc, InvImage.wf, Subrelation.wf
import Mathlib.Data.Prod.Lex                 -- Prod.Lex for lex orders
import Mathlib.Tactic.Linarith               -- linarith, Nat.cast_lt
import Mathlib.Tactic.Ring                   -- ring, ring_nf
import Mathlib.Algebra.Order.SuccPred        -- Order.lt_add_one_iff, add_one_le_of_lt
import Mathlib.SetTheory.Ordinal.Basic       -- ω, lt_wf, omega0_pos, one_lt_omega0, nat_lt_omega0, lt_omega0
import Mathlib.SetTheory.Ordinal.Arithmetic  -- pow_succ, pow_pos, add_lt_add_left, mul_lt_mul_of_pos_left,
                                             -- mul_le_mul_left', mul_le_mul_right', le_mul_right,
                                             -- add_le_add_left, add_le_add_right, add_lt_add_right
import Mathlib.SetTheory.Ordinal.Exponential -- opow, opow_pos, opow_add, opow_le_opow_right,
                                             -- opow_lt_opow_right, opow_lt_opow_of_lt_right,
                                             -- right_le_opow, left_le_opow, IsNormal.strictMono
import Mathlib.Data.Nat.Cast.Order.Basic     -- Nat.cast_le, Nat.cast_lt``` 

Keep **exactly** this list (trim only if an import disappears after upgrading Mathlib).

---

## 1  Extended Ordinal Toolkit (with exact signatures)

### 1.1 Basics & Positivity

| Lemma | Signature | Purpose |
|-------|-----------|---------|
| `omega0_pos` | `0 < omega0` | ω positive  |
| `one_lt_omega0` | `1 < omega0` | ω > 1  |
| `lt_omega0` | `o < omega0 ↔ ∃ n : ℕ, o = n` | finite-vs-infinite split  |
| `nat_lt_omega0` | `∀ n, (n : Ordinal) < omega0` | embed ℕ under ω  |
| `Nat.cast_le` / `Nat.cast_lt` | cast bridges | use after `simp` on ℕ/Ordinal  |
| `lt_wf` | well-foundedness of `<` | for `InvImage.wf` |

### 1.2 Addition & Successor

| Lemma | Signature | Purpose |
|-------|-----------|---------|
| `add_lt_add_left` | `a < b → c + a < c + b` | strict-mono left  |
| `add_lt_add_right` | `a < b → a + c < b + c` | strict-mono right |
| `add_le_add_left`  | `a ≤ b → c + a ≤ c + b` | weak-mono left |
| `add_le_add_right` | `a ≤ b → a + c ≤ b + c` | weak-mono right |
| `Order.lt_add_one_iff` | `x < y + 1 ↔ x ≤ y` | rewrite successor  |
| `Order.add_one_le_of_lt` | `x < y → x + 1 ≤ y` | strict → weak bridge  |
| **Absorption** |
| `Ordinal.one_add_of_omega0_le` | `ω ≤ p → 1 + p = p` | drop `1` on ∞  |
| `Ordinal.natCast_add_of_omega0_le` | `ω ≤ p → (n:ℕ)+p = p` | drop `n` on ∞  |

### 1.3 Multiplication (monotone helpers)

| Lemma | Signature | Purpose |
|-------|-----------|---------|
| `mul_lt_mul_of_pos_left` | `a < b → 0 < c → c*a < c*b` | strict left  |
| `mul_le_mul_left'` | `a ≤ b → c * a ≤ c * b` | weak left  |
| `mul_le_mul_right'` | `a ≤ b → a * c ≤ b * c` | weak right  |
| `le_mul_right` | `0 < b → a ≤ b * a` | absorb into product  |
| **Two-sided helper (define locally)** |
| `ord_mul_le_mul` | see code block below | combine the two one-sided lemmas  |

```lean
/-- Two–sided monotonicity of `(*)` for ordinals. -/
theorem ord_mul_le_mul {a b c d : Ordinal} (h₁ : a ≤ c) (h₂ : b ≤ d) :
    a * b ≤ c * d := by
  have h₁' := mul_le_mul_right' h₁ b
  have h₂' := mul_le_mul_left'  h₂ c
  exact le_trans h₁' h₂'
1.4 Exponentials (opow, Cantor-tower)
Lemma	Signature	Purpose
opow_pos	0 < a → 0 < a ^ b	positivity
opow_add	a ^ (b + c) = a ^ b * a ^ c	split exponent
opow_le_opow_right	0 < a → b ≤ c → a ^ b ≤ a ^ c	weak-mono exponent
opow_lt_opow_of_lt_right	0 < a → b < c → a ^ b < a ^ c	strict-mono exponent
right_le_opow	1 < a → b ≤ a ^ b	base dominates
left_le_opow	0 < b → a ≤ a ^ b	exponent dominates
pow_succ (for Nat-bases)	a^(k+1) = a^k * a	unfold one step
pow_pos	0 < a → 0 < a^b	Nat powers

2 Local Bridges & Utility Lemmas
lean
Copy
Edit
@[simp] theorem natCast_le {m n : ℕ} :
    ((m : Ordinal) ≤ (n : Ordinal)) ↔ m ≤ n := Nat.cast_le
@[simp] theorem natCast_lt {m n : ℕ} :
    ((m : Ordinal) < (n : Ordinal)) ↔ m < n := Nat.cast_lt

/-- Decide “finite or ≥ ω”. -/
theorem eq_nat_or_omega0_le (p : Ordinal) :
    (∃ n : ℕ, p = n) ∨ omega0 ≤ p := by
  classical
  cases lt_or_ge p omega0 with
  | inl h => rcases (lt_omega0).1 h with ⟨n, rfl⟩; exact Or.inl ⟨n, rfl⟩
  | inr h => exact Or.inr h
(Original versions already appear in § 8.2.1 of AGENT.md )

3 μ-Measure Cookbook (termination proofs)
Goal skeleton: show ω^k * (t + 1) + 1 ≤ ω^(t + K) then stack inequalities.

Finite / Infinite split:
eq_nat_or_omega0_le t → proves t < ω ⇒ small case OR ω ≤ t ⇒ absorption usable.

Collapse finite left-adds when ω ≤ p:
one_left_add_absorb, nat_left_add_absorb.

Raise tower:
mul_lt_mul_of_pos_left + opow_add + opow_le_opow_right.

Successor bridge whenever Lean rewrites to Order.succ:
Order.lt_add_one_iff, Order.add_one_le_of_lt.

Product padding:
ord_mul_le_mul for mixed-factor monotonicity.

Follow this chain for every rule in Termination.lean and the ugly inequalities fall into place.
(The template steps mirror § 8.2.3 of the proof manual )

4 Standard Debug Trace (copy into .lean when a goal explodes)

-- Print goal + locals
#check_goal
-- If you see Order.succ, use:
rw [Order.lt_add_one_iff] at *
-- Confirm coefficient side:
have : 0 < omega0 := omega0_pos
-- Push inequality through multiplication:
have h := mul_le_mul_left' ‹_› _
-- Finish with ≤ trans
exact le_trans h ‹_›
5 Common Lean Errors → One-line Fixes
Error fragment	Means	Fix
“expected MulRightMono”	wrong arg order in mul_le_mul_right'	supply (proof) (factor)
Order.succ p shows up	Lean canonicalised p + 1	rewrite via lt_add_one_iff / restate lemma
1 + A ≤ A fails	tried to absorb +1 before proving ω ≤ A	first show omega0 ≤ A, then use absorption
universe mismatch on opow	base isn’t positive	add have : 0 < ω := omega0_pos

6 Ready-made Snippets (inlined)
Everything from § 8.4 of AGENT.md is still valid (size measure, WF via InvImage, normalize-join) .

7 Sanity Checklist — Pass before every commit
Imports ⊆ whitelist (§0).

No axiom, sorry, admit, unsafe.

Kernel untouched.

Every ordinal lemma appears in §§ 1-2 or is proven locally.

All successor rewrites handled (no raw Order.succ surprises).

Termination rules: proven μ b < μ a.

normalize + confluent_via_normalize compile.

Fuzz tests terminate.

TL;DR mantra

“Branch finite vs ω, absorb, raise the ω-tower, bridge successors, and keep argument order straight.”
