# O6 Consolidated Guide: The Project Bible
*Version: 2025-08-07. Authoritative, consolidated guide for the OperatorKernelO6 project.*

---

## 1. Prime Directive & Project Goals

### 1.1. The Mission
This project is dedicated to creating a **procedural, axiom-free, numeral-free, and boolean-free** mathematical foundation. In this system, everything—logic, arithmetic, provability, and Gödelian diagonalization—is built from a single inductive `Trace` type and a deterministic normalizer.

### 1.2. Core Principles
- **Axiom Freedom:** The system uses no external logical or arithmetic schemes (e.g., no Peano axioms, no law of excluded middle imported from outside).
- **Procedural Truth:** A proposition is considered "true" if and only if its corresponding `Trace` representation normalizes to the `void` trace. Truth is a result of a deterministic computation.
- **Emergent Structures:** Complex mathematical objects emerge from the simple rules of the kernel. Numerals are chains of `delta` constructors, negation is the cancellation of identical terms via `merge`, and proofs themselves are encoded as `Trace` objects.
- **Deterministic Geometry:** The system is provably terminating (Strong Normalization) and confluent, meaning every `Trace` has a unique, canonical normal form.

---

## 2. The Sacred Kernel

The `OperatorKernelO6` kernel is immutable. It consists of one inductive type and eight reduction rules. It must not be altered.

```lean
namespace OperatorKernelO6

-- The single foundational type.
inductive Trace : Type
| void : Trace
| delta : Trace → Trace
| integrate : Trace → Trace
| merge : Trace → Trace → Trace
| recΔ : Trace → Trace → Trace → Trace
| eqW : Trace → Trace → Trace

open Trace

-- The 8 deterministic reduction rules.
inductive Step : Trace → Trace → Prop
| R_int_delta : ∀ t, Step (integrate (delta t)) void
| R_merge_void_left : ∀ t, Step (merge void t) t
| R_merge_void_right : ∀ t, Step (merge t void) t
| R_merge_cancel : ∀ t, Step (merge t t) t
| R_rec_zero : ∀ b s, Step (recΔ b s void) b
| R_rec_succ : ∀ b s n, Step (recΔ b s (delta n)) (merge s (recΔ b s n))
| R_eq_refl : ∀ a, Step (eqW a a) void
| R_eq_diff : ∀ a b, Step (eqW a b) (integrate (merge a b))

-- Transitive closure of the Step relation.
inductive StepStar : Trace → Trace → Prop
| refl : ∀ t, StepStar t t
| tail : ∀ {a b c}, Step a b → StepStar b c → StepStar a c

-- A Trace is in Normal Form if it cannot take a Step.
def NormalForm (t : Trace) : Prop := ¬ ∃ u, Step t u

end OperatorKernelO6
```

---

## 3. The Strong Normalization Proof (The Full Story)

Strong Normalization (SN) is the guarantee that every possible sequence of reductions on any `Trace` will eventually terminate. The proof of SN is the project's first major milestone.

### 3.1. Part A: The Flawed Path (and Lessons Learned)

The initial attempt at the SN proof used a single ordinal measure function, `μ : Trace → Ordinal`. The goal was to show that for every reduction `Step t u`, we have `μ u < μ t`. This approach failed due to a subtle but fatal flaw in ordinal arithmetic.

- **The Flaw:** The proof for the `R_rec_succ` rule required showing `μ(merge s (recΔ b s n)) < μ(recΔ b s (delta n))`. This ultimately relied on an inequality of the form `a + c < b + c` being derivable from `a < b`. However, **ordinal addition is not right-cancellative**. The general statement `a < b → a + c < b + c` is **false** for ordinals.
- **The Consequence:** The original proof contained a hidden, unsound assumption (`rec_succ_bound`) that was masked by proof-specific tactics. This rendered the entire proof invalid. This discovery was a critical turning point, forcing a move to a more robust method.

### 3.2. Part B: The Correct Path (Lexicographic Measure)

The correct and current approach uses a **lexicographic measure**. Instead of mapping a `Trace` to a single ordinal, we map it to a pair `(κ, μ)`, where `κ` is a natural number and `μ` is an ordinal.

`μκ : Trace → Nat × Ordinal`

The lexicographic order `(κ₁, μ₁) < (κ₂, μ₂)` holds if:
- `κ₁ < κ₂` (the primary measure decreases), OR
- `κ₁ = κ₂` AND `μ₁ < μ₂` (the primary measure is stable, and the secondary measure decreases).

This solves the problem of the `R_rec_succ` rule perfectly.

- **The `κ` (kappa) Measure:** `κ` counts the nesting depth of `delta` constructors.
  ```lean
  def kappa : Trace → Nat
  | void => 0
  | delta t => kappa t + 1
  | integrate t => kappa t
  | merge a b => max (kappa a) (kappa b)
  | recΔ b s n => max (kappa b) (max (kappa s) (kappa n))
  | eqW a b => max (kappa a) (kappa b)
  ```
- **The `μ` (mu) Measure:** `μ` is the complex ordinal measure from the original attempt. It is now the secondary measure.
  ```lean
  noncomputable def mu : Trace → Ordinal.{0}
  | .void        => 0
  | .delta t     => (omega0 ^ 5) * (mu t + 1) + 1
  | .integrate t => (omega0 ^ 4) * (mu t + 1) + 1
  | .merge a b   => (omega0 ^ 3) * (mu a + 1) + (omega0 ^ 2) * (mu b + 1) + 1
  | .recΔ b s n  => omega0 ^ (mu n + mu s + 6) + omega0 * (mu b + 1) + 1
  | .eqW a b     => omega0 ^ (mu a + mu b + 9) + 1
  ```

- **How it Works:**
  - For the `R_rec_succ` rule, `κ` strictly decreases, so the lexicographic measure decreases regardless of what `μ` does.
  - For all other 7 rules, `κ` remains the same, so the proof must show that `μ` decreases. This reuses the valid parts of the original proof attempt.

---

## 4. The Implementation Cookbook (Proving SN)

To prove strong normalization, we must show that `μκ u < μκ t` for all 8 `Step` rules.

### 4.1. Foundational Lemmas
1.  **`wf_LexNatOrd`**: Prove that the lexicographic order on `Nat × Ordinal` is well-founded. This is a one-liner using `WellFounded.prod_lex`.
2.  **`mu_to_mu_kappa`**: Create a helper lemma that lifts a `μ`-decrease to a `μκ`-decrease when `κ` is equal. `κ u = κ t → μ u < μ t → μκ u < μκ t`.

### 4.2. Decrease Proofs for the 8 Rules

-   **`R_int_delta`**, **`R_merge_void_left`**, **`R_merge_void_right`**, **`R_merge_cancel`**, **`R_rec_zero`**, **`R_eq_refl`**, **`R_eq_diff`**:
    -   **Strategy:** For these 7 rules, prove that `κ` does not increase (`κ u ≤ κ t`). Then, prove that `μ` strictly decreases (`μ u < μ t`). The `mu_to_mu_kappa` lemma then proves the final goal. The proofs for the `μ` decrease are complex and rely on the Ordinal Toolkit.

-   **`R_rec_succ`**:
    -   **Strategy:** This is the `κ`-decreasing case. The proof involves showing that `κ(merge s (recΔ b s n)) < κ(recΔ b s (delta n))`. This requires showing `max (κ s) (κ (recΔ b s n)) < κ n + 1`, which follows from the definition of `max` and properties of natural numbers.

### 4.3. The μ-Measure Playbook
When proving `μ u < μ t`, follow this standard procedure:
1.  **Assert Positivity:** Start with `have ωpos : 0 < omega0 := omega0_pos`.
2.  **Lift via Exponents:** Use `Ordinal.opow_le_opow_right` for `≤` and the local `opow_lt_opow_right` for `<` to move inequalities into the exponents of `omega0`.
3.  **Split Terms:** Use `opow_add` to split exponents (`a^(b+c) = a^b * a^c`) so that product monotonicity rules can be applied.
4.  **Apply Monotonicity:** Use `Ordinal.mul_le_mul_iff_left` and its variants to cancel terms across an inequality.
5.  **Absorb Addends:** Use `(n:Ordinal) + p = p` once you establish `omega0 ≤ p`.
6.  **Bridge Successors:** Convert between `<` and `≤` using `Order.lt_add_one_iff` (`x < y + 1 ↔ x ≤ y`).
7.  **Clean Up:** Use `linarith` or `ring` for side-goals involving pure `Nat` or `Int` arithmetic.

---

## 5. The Ordinal Toolkit (Authoritative)

This section contains the complete, verified list of all allowed imports, lemmas, and naming conventions for working with ordinals in `mathlib`.

### 5.1. Import Whitelist
```lean
import OperatorKernelO6.Kernel
import Init.WF
import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
```

### 5.2. Lemma Catalogue & Naming Rules

-   **Basics & Positivity:**
    -   `omega0_pos : 0 < omega0`
    -   `one_lt_omega0 : 1 < omega0`
    -   `lt_omega0 : o < omega0 ↔ ∃ n : ℕ, o = n`

-   **Addition & Successor:**
    -   `add_lt_add_left : a < b → c + a < c + b`
    -   `add_le_add_left : a ≤ b → c + a ≤ c + b`
    -   `Order.lt_add_one_iff : x < y + 1 ↔ x ≤ y` (Use `Order.` prefix)
    -   `Order.add_one_le_of_lt : x < y → x + 1 ≤ y` (Use `Order.` prefix)
    -   `Ordinal.one_add_of_omega_le`, `Ordinal.natCast_add_of_omega_le`: For absorption.

-   **Multiplication (Ordinal-Specific):**
    -   `Ordinal.mul_lt_mul_of_pos_left : a < b → 0 < c → c * a < c * b`
    -   `Ordinal.mul_le_mul_iff_left : c * a ≤ c * b ↔ a ≤ b`
    -   **DO NOT USE** generic `mul_le_mul_left`. Use the `Ordinal.`-prefixed or primed versions.

-   **Exponentiation (ω-powers):**
    -   `opow_add : a ^ (b + c) = a ^ b * a ^ c`
    -   `Ordinal.opow_le_opow_right : 0 < a → b ≤ c → a ^ b ≤ a ^ c` (Use `Ordinal.` prefix)
    -   `opow_lt_opow_right {b c} (h : b < c) : omega0 ^ b < omega0 ^ c` (Local helper lemma)

### 5.3. Do-Not-Use List
-   **`add_lt_add_right`**: False for ordinals. The root of the original proof's failure.
-   **Generic `mul_le_mul_left`**: Use ordinal-specific versions from `Mathlib.SetTheory.Ordinal.Arithmetic`.
-   **`le_of_not_lt`**: Deprecated in `mathlib`. Use `le_of_not_gt`.

---

## 6. Key Discoveries & Agent Protocol

### 6.1. Revolutionary Technical Discoveries
1.  **Universe Level Mastery (`Ordinal.{0}`):** The most critical code fix was changing the signature of the `mu` function from `Trace → Ordinal` to `Trace → Ordinal.{0}`. This resolved over 25 cascading universe polymorphism errors throughout the codebase.
2.  **Pattern Analysis is Key:** The most effective development strategy is to find working examples of syntax and proof patterns in existing, verified files (like `Termination_C.lean` or `mathlib` source) and copy them exactly. **Never guess Lean 4 syntax.**
3.  **Direct Monotonicity Proofs:** When dealing with non-commutative ordinal arithmetic, avoid trying to reorder terms. Instead, build proofs using direct, one-sided monotonicity lemmas like `add_le_add_right` or `add_lt_add_left`.

### 6.2. Agent Interaction Protocol
-   **Allowed Outputs:** `PLAN`, `CODE`, `SEARCH`, `CONSTRAINT BLOCKER`.
-   **Search-First Development:** Before writing any code that uses a lemma, **SEARCH** for it in this guide or the project files.
    -   If found, use the exact name.
    -   If not found, raise a `CONSTRAINT BLOCKER`. Do not invent or guess lemma names.
-   **Kernel is Sacred:** Do not edit, rename, or add to the kernel definitions without explicit approval.
-   **No Axioms:** Never introduce `sorry`, `axiom`, `admit`, or `unsafe`.
-   **If Unsure, Ask:** If a path seems blocked or a rule seems ambiguous, raise a `CONSTRAINT BLOCKER` with a clear question. It is better to pause and clarify than to proceed with a flawed assumption.
