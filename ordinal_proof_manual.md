## Operator Kernel O6: Ordinal Termination and Proof Manual (v1.0)

---

### ✨ Key Technical Discovery: `Order.succ` vs `+ 1` Collapse

---

#### 🔍 Root Issue:

- Your `mu` function uses `+ 1` throughout: `μ t = ... + 1`.
- But Lean's **type system** auto-converts `p + 1` into `Order.succ p` in many proof contexts.

#### ⛔ Consequence:

- Lemmas expect `p + 1`, but goal is `Order.succ p`.
- Type mismatch: `k + (p + 1)` can't unify with `k + Order.succ p`.

#### 💣 Smoking Gun Example:

```lean
Expected:   3 + Order.succ p = Order.succ p
Got:        3 + p + 1 = p + 1
```

#### ⚠ Symptom:

- Seemingly correct proof collapses to `True : Prop`
- Math is fine, Lean's **type-level conversion** sabotages the chaining.

#### ✔️ Fix:

- Work directly with `Order.succ`, or bridge explicitly using:

```lean
theorem lt_add_one_of_le {x y : Ordinal} (h : x ≤ y) : x < y + 1 :=
  (Order.lt_add_one_iff (x := x) (y := y)).2 h
```

- Or, prove the lemmas **with Order.succ in mind** instead of `+1`.

---

### 🔹 Confirmed Type System Behavior

#### When proving:

```lean
k + (p + 1) ≤ p + (k + 1)
```

Lean converts:

```lean
p + 1 → Order.succ p
```

But the helper lemmas you wrote only work on `+ 1`, not `Order.succ`, so:

```lean
k + (p + 1) ≠ k + Order.succ p
```

Even though mathematically:

```lean
k + (p + 1) = p + 1
```

The type system blocks unification.

---

### 🏋️ Example Workflow that Now Works

#### Goal:

```lean
ω^2 * (μ t + 1) + 1 ≤ A := ω ^ (μ n.delta + 6)
```

#### Steps:

1. Use `opow_le_opow_right (le_of_lt (two_lt_mu_delta_add_six n))` correctly
   - Fix: remove `omega0_pos`, set `a := omega0` explicitly
2. Use `mul_le_mul_right'` and `mul_le_mul_left'` with universe annotations (or bundle in helper `ord_mul_le_mul`)
3. Collapse finite left-adds with `nat_left_add_absorb`
4. Use `add_le_add_right` correctly:
   ```lean
   add_le_add_right (mul_le_mul_left' omega_le _) 1
   ```
5. Close with `Order.add_one_le_of_lt` if needed to bridge strict/weak successor

---

## 8. Canonical Imports, Lemmas & Snippets (NO DROPS)

### 8.1 Import Whitelist

```lean
import OperatorKernelO6.Kernel              -- kernel
import Init.WF                               -- WellFounded, Acc, InvImage.wf, Subrelation.wf
import Mathlib.Data.Prod.Lex                 -- Prod.Lex for lex orders
import Mathlib.Tactic.Linarith               -- linarith, Nat.cast_lt
import Mathlib.Tactic.Ring                   -- ring, ring_nf
import Mathlib.Algebra.Order.SuccPred        -- Order.lt_add_one_iff, add_one_le_iff
import Mathlib.SetTheory.Ordinal.Basic       -- ω, lt_wf, omega0_pos, one_lt_omega0, nat_lt_omega0, lt_omega0
import Mathlib.SetTheory.Ordinal.Arithmetic  -- pow_succ, pow_pos, add_lt_add_left, mul_lt_mul_of_pos_left,
                                             -- mul_le_mul_left', mul_le_mul_right', le_mul_right
import Mathlib.SetTheory.Ordinal.Exponential -- opow, opow_pos, opow_add, opow_le_opow_right,
                                             -- right_le_opow, left_le_opow, IsNormal.strictMono
import Mathlib.Data.Nat.Cast.Order.Basic     -- Nat.cast_le, Nat.cast_lt
```

---

### 8.2 Ordinal Toolkit (with Signatures)

| Lemma / Theorem                      | Signature (exact)                         | Purpose                         |
| ------------------------------------ | ----------------------------------------- | ------------------------------- |
| omega0\_pos                          | `0 < omega0`                              | ω positive                      |
| one\_lt\_omega0                      | `1 < omega0`                              | ω > 1                           |
| lt\_omega0                           | `o < ω ⇔ ∃ n, o = n`                      | Finite ordinal characterization |
| nat\_lt\_omega0                      | `∀ n, (n : Ordinal) < omega0`             | Embed ℕ below ω                 |
| Nat.cast\_le / Nat.cast\_lt          | `((m : Ordinal) ≤ (n : Ordinal)) ⇔ m ≤ n` | Cast bridges                    |
| pow\_succ                            | `a ^ (k+1) = a ^ k * a`                   | Exponent step                   |
| pow\_pos                             | `0 < a → 0 < a ^ b`                       | Power positivity                |
| add\_lt\_add\_left                   | `a < b → c + a < c + b`                   | Add-left mono                   |
| mul\_lt\_mul\_of\_pos\_left          | `a < b → 0 < c → c*a < c*b`               | mul-left strict mono            |
| mul\_le\_mul\_left'                  | `a ≤ b → c*a ≤ c*b`                       | mul-left mono (≤)               |
| mul\_le\_mul\_right'                 | `a ≤ b → a*c ≤ b*c`                       | mul-right mono (≤)              |
| le\_mul\_right                       | `0 < b → a ≤ b*a`                         | absorb into product             |
| opow\_pos                            | `0 < a → 0 < a ^ b`                       | opow positivity                 |
| opow\_add                            | `a ^ (b + c) = a ^ b * a ^ c`             | opow exponent add               |
| opow\_le\_opow\_right                | `0 < a → b ≤ c → a ^ b ≤ a ^ c`           | exponent mono (right)           |
| right\_le\_opow                      | `1 < a → b ≤ a ^ b`                       | base dominates exponent         |
| left\_le\_opow                       | `0 < b → a ≤ a ^ b`                       | exponent dominates base         |
| IsNormal.strictMono                  | `<strictMono f>`                          | normal func mono                |
| Order.lt\_add\_one\_iff              | `x < y + 1 ⇔ x ≤ y`                       | +1 ↔ Order.succ bridge          |
| Order.add\_one\_le\_of\_lt           | `x < y → x + 1 ≤ y`                       | ≤ successor intro               |
| Ordinal.one\_add\_of\_omega0\_le     | `ω ≤ p → 1 + p = p`                       | absorb 1 on ∞                   |
| Ordinal.natCast\_add\_of\_omega0\_le | `ω ≤ p → n + p = p`                       | absorb n on ∞                   |

---

#### 8.2.1 Local Lemmas

```lean
@[simp] theorem natCast_le {m n : ℕ} : ((m : Ordinal) ≤ (n : Ordinal)) ⇔ m ≤ n := Nat.cast_le
@[simp] theorem natCast_lt {m n : ℕ} : ((m : Ordinal) < (n : Ordinal)) ⇔ m < n := Nat.cast_lt

theorem eq_nat_or_omega0_le (p : Ordinal) : (∃ n, p = n) ∨ ω ≤ p := by
  classical; cases lt_or_ge p ω with
  | inl h => rcases (lt_omega0).1 h with ⟨n, rfl⟩; exact Or.inl ⟨n, rfl⟩
  | inr h => exact Or.inr h

theorem one_left_add_absorb {p : Ordinal} (h : ω ≤ p) : 1 + p = p :=
  by simpa using Ordinal.one_add_of_omega0_le h

theorem nat_left_add_absorb {n : ℕ} {p : Ordinal} (h : ω ≤ p) : (n : Ordinal) + p = p :=
  by simpa using Ordinal.natCast_add_of_omega0_le h
```

#### 8.2.2 Two-Sided `(*)` Monotonicity (no built-in `mul_le_mul`)

```lean
theorem ord_mul_le_mul {a b c d : Ordinal} (h1 : a ≤ c) (h2 : b ≤ d) :
    a * b ≤ c * d := by
  have h1' := mul_le_mul_right' h1 b
  have h2' := mul_le_mul_left' h2 c
  exact le_trans h1' h2'
```

#### 8.2.3 Measure Proof Template

- Use `μ : Trace → Ordinal`
- Show: `Step a b → μ b < μ a`
- Strategy:
  - Reduce to `ω^k * (x+1) ≤ ω^{x + k'} + 1`
  - Collapse left adds: `nat_left_add_absorb`, `one_left_add_absorb`
  - Multiply: `ord_mul_le_mul`, `mul_le_mul_left'`, etc.
  - Handle `+1` carefully: use `Order.lt_add_one_iff` instead of `+1`.

---

> Use this as a reference for any termination or ordinal-bound proof. All known Lean type system collapses stem from p + 1 → Order.succ p unless controlled.

