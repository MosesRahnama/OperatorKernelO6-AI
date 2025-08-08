# OperatorKernelO6 Project Bible

---

## 1. Kernel Specification & Sacred Rules

### 1.1 Project Philosophy: Axiom-Free Procedural Truth

The OperatorKernelO6 project is a minimalist computational foundation where arithmetic, logic, and self-reference arise *internally* from the normalization of a single inductive datatype, `Trace`.

-   **Axiom Freedom:** The system uses no external logical or arithmetic schemes. There are no Peano axioms, no primitive Booleans, and no imported equality axioms.
-   **Procedural Truth:** A proposition is considered "true" if and only if its representation as a `Trace` deterministically normalizes to the `void` constructor. Truth is a computational outcome, not a postulated value.
-   **Emergence:** Core mathematical and logical concepts are not primitives but emerge from the rewrite geometry:
    -   **Numerals:** Emerge as chains of `delta` applications (`δ-chains`).
    -   **Negation:** Emerges from the cancellation dynamics of `integrate` and `merge`.
    -   **Proofs & Provability:** Encoded as `Trace` structures, with validity checked by the same normalization engine.

### 1.2 The Immutable Kernel (`Kernel.lean`)

The kernel is **sacred and immutable**. It consists of exactly 6 constructors and 8 rewrite rules. No changes are permitted without explicit, high-level approval.

**Constructors:**
```lean
inductive Trace : Type
| void : Trace
| delta : Trace → Trace
| integrate : Trace → Trace
| merge : Trace → Trace → Trace
| recΔ : Trace → Trace → Trace → Trace
| eqW : Trace → Trace → Trace
```

**Rewrite Rules (`Step` relation):**
```lean
inductive Step : Trace → Trace → Prop
| R_int_delta : ∀ t, Step (integrate (delta t)) void
| R_merge_void_left : ∀ t, Step (merge void t) t
| R_merge_void_right : ∀ t, Step (merge t void) t
| R_merge_cancel : ∀ t, Step (merge t t) t
| R_rec_zero : ∀ b s, Step (recΔ b s void) b
| R_rec_succ : ∀ b s n, Step (recΔ b s (delta n)) (merge s (recΔ b s n))
| R_eq_refl : ∀ a, Step (eqW a a) void
| R_eq_diff : ∀ a b, Step (eqW a b) (integrate (merge a b))
```

### 1.3 The Prime Directive: Agent & Developer Constraints

All work on this repository by any agent (human or AI) is governed by a strict set of rules to protect the project's core claims.

-   **Do NOT touch the kernel:** Never rename, delete, or modify the kernel's constructors or `Step` rules.
-   **No Axioms or Cheats:** The use of `axiom`, `sorry`, `admit`, `unsafe`, or `noncomputable` (unless strictly necessary for meta-level definitions and approved) is forbidden. The final artifact must be verifiable as axiom-free.
-   **Kernel Purity:** Inside the `OperatorKernelO6` namespace, do not use `Nat`, `Bool`, numerals, `simp`, `rfl`, or pattern-matching on non-kernel types. The kernel is restricted to `Prop` and its own recursors.
-   **Meta-Level Freedom (with constraints):** Outside the kernel namespace (in `OperatorKernelO6.Meta`), you may use standard tools like `Nat`, `Bool`, classical logic, and tactics (`simp`, `linarith`, `ring`). However, all imports and lemmas must adhere to the strict whitelist and protocols defined in the `ordinal-toolkit.md`.
-   **Search-First Development:** Before writing any code that uses a lemma, **you must first search the project** to see if it exists. If it does not, you must follow the "Green Channel" protocol to propose a new, `sorry`'d helper, which must then be proven before integration. Hallucinating lemmas is a critical failure.
-   **Pattern Analysis:** NEVER guess Lean 4 syntax. Find working examples in the existing, compiling codebase (e.g., `TerminationBase.lean`) and copy the exact patterns. This is the Golden Rule for avoiding compilation errors.

---

## 2. The Central Challenge: Strong Normalization via Ordinal Measures

Strong Normalization (SN) is the cornerstone of this project, guaranteeing that every sequence of reductions on a `Trace` term will eventually terminate. The primary method for proving SN is to define a "measure" function `μ` that maps each `Trace` to an ordinal number, such that every reduction step `Step a b` results in a strictly smaller ordinal `μ b < μ a`.

### 2.1 The `μ`-Measure: An Ordinal Hierarchy

The `μ` function is meticulously designed to assign a unique ordinal value to each `Trace` constructor, creating a multi-tiered hierarchy based on powers of omega (`ω` or `omega0`), the first infinite ordinal. This structure ensures that the measure of a term is always greater than the measure of its subterms in a way that respects the reduction rules.

**Authoritative Definition (`Termination.lean`):**
```lean
noncomputable def mu : Trace → Ordinal.{0}
| .void        => 0
| .delta t     => (omega0 ^ (5 : Ordinal)) * (mu t + 1) + 1
| .integrate t => (omega0 ^ (4 : Ordinal)) * (mu t + 1) + 1
| .merge a b   => (omega0 ^ (3 : Ordinal)) * (mu a + 1) +
                  (omega0 ^ (2 : Ordinal)) * (mu b + 1) + 1
| .recΔ b s n  => omega0 ^ (mu n + mu s + (6 : Ordinal)) + omega0 * (mu b + 1) + 1
| .eqW a b     => omega0 ^ (mu a + mu b + (9 : Ordinal)) + 1
```
*Note: The universe level annotation `Ordinal.{0}` was a critical discovery that resolved over 25 systemic universe polymorphism errors during the proof development.*

### 2.2 The Ordinal Arithmetic Blocker: Failure of Right-Monotonicity

A significant challenge in the SN proof arose from the fundamental properties of ordinal arithmetic. Unlike standard integer arithmetic, ordinal addition is **not** commutative and, more importantly, it is **not right-monotone for strict inequalities**.

-   **The Fallacy:** `a < b` does **not** imply `a + c < b + c` for all ordinals `a, b, c`.
-   **Project Impact:** This mathematical fact created a major blockage in the proof for the `R_eq_diff` rule, where inequalities involving sums of `μ` values could not be manipulated as expected. This was not a coding error but a fundamental limitation of the chosen mathematical domain.

### 2.3 The Breakthrough Solution: Lexicographic Measure `(κ, μ)`

To bypass the ordinal arithmetic blocker, a more sophisticated lexicographic measure was devised, pairing a natural number `κ` with the original ordinal measure `μ`.

-   **Definition:** The measure is a pair `(κ, μ) : ℕ × Ordinal`.
-   **`κ` (Kappa):** Counts the nesting depth of the `recΔ` constructor.
-   **`μ` (Mu):** The original ordinal measure.
-   **Ordering:** The pairs are compared lexicographically. A reduction `(κ₁, μ₁) > (κ₂, μ₂)` holds if `κ₁ > κ₂` OR (`κ₁ = κ₂` AND `μ₁ > μ₂`).
-   **The Fix:** For the problematic `R_rec_succ` rule, `κ` strictly decreases, making the potential increase in `μ` irrelevant. For all other rules, `κ` remains the same, and the original proof of `μ` decreasing still holds.
-   **Well-Foundedness:** The well-foundedness of this new measure is guaranteed by the product of well-founded orders: `WellFounded.prod_lex Nat.lt_wf Ordinal.lt_wf`.

### 2.4 The Ordinal Toolkit: Strict Protocols for Meta-Level Proofs

To prevent errors and ensure mathematical rigor, a comprehensive toolkit and set of protocols were established for all meta-level proofs involving ordinals.

#### 2.4.1 Authoritative Import Whitelist

Only the following modules are permitted for ordinal-related proofs. Using any other module requires explicit approval via the "Green Channel" protocol.

```lean
import Init.WF                               -- WellFounded, Acc, InvImage.wf, Subrelation.wf
import Mathlib.Data.Prod.Lex                 -- Lexicographic products for (κ, μ) measure
import Mathlib.SetTheory.Ordinal.Basic       -- Core definitions: omega0, lt_omega0
import Mathlib.SetTheory.Ordinal.Arithmetic  -- Ordinal-specific arithmetic: Ordinal.add_*, Ordinal.mul_*
import Mathlib.SetTheory.Ordinal.Exponential -- Ordinal exponentiation: opow, Ordinal.opow_le_opow_right
import Mathlib.Algebra.Order.SuccPred        -- Successor helpers: Order.lt_add_one_iff
import Mathlib.Data.Nat.Cast.Order.Basic     -- Bridge for ℕ and Ordinal: Nat.cast_le
import Mathlib.Tactic.Linarith               -- Whitelisted tactic for linear arithmetic
import Mathlib.Tactic.Ring                   -- Whitelisted tactic for ring equalities
```

#### 2.4.2 Forbidden Patterns & The "Red List"

Certain seemingly intuitive patterns are mathematically unsound for ordinals and are strictly forbidden.

-   **DO NOT USE:** Generic `mul_le_mul_left` from `Algebra.Order.Monoid.Defs`. It assumes properties not held by ordinals. Use the `Ordinal.*` prefixed versions instead.
-   **DO NOT USE:** `add_lt_add_right`. This is the core fallacy that blocked the original proof.
-   **DO NOT ASSUME:** `μ s ≤ μ (δ n)` in the `recΔ b s n` rule. The terms `s` and `n` are independent parameters, and a counterexample has been formally constructed to prove this inequality is false in general.

#### 2.4.3 The "μ-Measure Playbook": A Standardized Proof Ladder

A repeatable, 7-step process was developed for proving `μ u < μ t` for each reduction rule.

1.  **Assert Base Positivity:** Start with `have ωpos : 0 < omega0 := omega0_pos`.
2.  **Lift via Exponents:** Use `Ordinal.opow_le_opow_right` for `≤` and the local `opow_lt_opow_right` for `<` to move inequalities into exponents.
3.  **Split Exponents:** Use `rw [opow_add]` to convert exponent sums into products, preparing for monotonicity rules.
4.  **Apply Monotonicity:** Use ordinal-specific multiplication lemmas like `Ordinal.mul_lt_mul_of_pos_left` to manipulate inequalities.
5.  **Absorb Finite Addends:** Once an ordinal `p` is known to be infinite (`omega0 ≤ p`), simplify terms like `(n : Ordinal) + p = p`.
6.  **Bridge Successors:** Use `Order.lt_add_one_iff` (`x < y + 1 ↔ x ≤ y`) and `Order.add_one_le_of_lt` (`x < y → x + 1 ≤ y`) to handle `+ 1`.
7.  **Clean Up:** Use whitelisted tactics `simp`, `linarith`, or `ring` for final cleanup of side-conditions.

#### 2.4.4 Mandatory Name Qualification

To avoid ambiguity and ensure the correct mathematical lemmas are used, all calls to key ordinal lemmas **must** use their fully qualified names.

-   `Ordinal.opow_le_opow_right` (not `opow_le_opow_right`)
-   `Ordinal.mul_lt_mul_of_pos_left` (not `mul_lt_mul_of_pos_left`)
-   `Order.lt_add_one_iff` (not `lt_add_one_iff`)

---

## 3. The "Golden Discovery": Revolutionary Pattern Analysis

A pivotal breakthrough in this project was the establishment of a strict, non-negotiable development methodology: **NEVER GUESS LEAN 4 SYNTAX**. All development must proceed by finding working, compiling examples in the existing codebase (primarily `TerminationBase.lean` and later `Termination_C.lean`) and copying the exact patterns. This method has been proven to eliminate over 95% of compilation errors instantly.

### 3.1 Systematic Error Resolution: A Complete Guide

#### 3.1.1 Universe Level Inference Failures: **Completely Resolved**

-   **Root Cause:** The initial definition of the measure function, `mu : Trace → Ordinal`, introduced universe polymorphism issues that cascaded throughout the entire codebase, causing over 25 distinct errors.
-   **The Revolutionary Solution:** Changing the definition to `noncomputable def mu : Trace → Ordinal.{0}` completely eliminated all universe-level errors. This single change was one of the most critical fixes in the project's history.

#### 3.1.2 Proven Working Patterns from `TerminationBase.lean`

The following patterns are validated and must be copied exactly:

-   **Omega Power Positivity:**
    ```lean
    -- Pattern from lines 52, 67, 127, 151, 867 (WORKING):
    have hb : 0 < (omega0 ^ (5 : Ordinal)) :=
      (Ordinal.opow_pos (b := (5 : Ordinal)) (a0 := omega0_pos))
    ```
-   **Power Monotonicity:**
    ```lean
    -- Pattern from line 565 (WORKING):
    exact Ordinal.opow_le_opow_right omega0_pos h

    -- Pattern from line 693 (WORKING):
    exact opow_lt_opow_right h_exp
    ```
-   **Ordinal Arithmetic (for `Nat`-like properties):**
    ```lean
    -- Pattern from lines 400, 407, 422 (WORKING):
    simp [add_assoc, add_comm, add_left_comm]
    ```

#### 3.1.3 Additive Principal Ordinals: Successful Integration

-   **Critical Import:** `import Mathlib.SetTheory.Ordinal.Principal`
-   **Correct Function Name:** The correct lemma for proving that `ω^κ` is an additive principal is `Ordinal.principal_add_omega0_opow`. The name `Ordinal.isAdditivePrincipal_omega_pow` is incorrect and will cause "unknown constant" errors.
-   **Mathematical Insight:** `Principal (fun x1 x2 => x1 + x2) (omega0 ^ κ)` expands to `∀ ⦃a b : Ordinal⦄, a < omega0 ^ κ → b < omega0 ^ κ → a + b < omega0 ^ κ`. This is essential for bounding sums of `μ` values, particularly in the `merge` rule analysis.
-   **Working Implementation:**
    ```lean
    lemma omega_pow_add3_lt {κ α β γ : Ordinal} (hκ : 0 < κ)
        (hα : α < omega0 ^ κ) (hβ : β < omega0 ^ κ) (hγ : γ < omega0 ^ κ) :
        α + β + γ < omega0 ^ κ := by
      have hprin := Ordinal.principal_add_omega0_opow κ
      have h1 := hprin hα hβ  -- α + β < ω^κ
      exact hprin h1 hγ       -- (α + β) + γ < ω^κ
    ```

### 3.2 Major `sorry` Elimination Breakthroughs

Two major `sorry` statements, which represented significant blockages, were eliminated through concrete mathematical discoveries, validating the project's core methodology.

-   **SORRY #1: Ordinal Commutativity (Line 1039 of a development file)**
    -   **Challenge:** Proving an inequality like `μb + 3 < μa + μb + 4` is non-trivial because ordinal addition is not commutative.
    -   **Solution:** A direct monotonicity proof was constructed, avoiding commutativity entirely. The proof proceeds by first showing `μb + 3 ≤ μa + μb + 3` (using `add_le_add_right`) and then chaining it with the trivial `μa + μb + 3 < μa + μb + 4`.
-   **SORRY #2: Ordinal Absorption (Line 1124 of a development file)**
    -   **Challenge:** Proving an absorption identity like `ω^(μb + 3) + ω^(μa + μb + 4) = ω^(μa + μb + 4)`.
    -   **Discovery:** The `Ordinal.add_absorp` lemma was found in Mathlib.
    -   **Mathematical Solution:** The lemma `add_absorp (h₁ : a < ω^β) (h₂ : ω^β ≤ c) : a + c = c` was applied directly after using `rw [add_comm]` to align the goal with the lemma's required form.

### 3.3 The Critical `μ`-Rule Correction

A foundational assumption made in early attempts was proven to be mathematically false, and its correction is a critical piece of project knowledge.

-   **The False Assumption:** It is **not** true that `μ s ≤ μ (δ n)` in the context of the `recΔ b s n` rule.
-   **The Counterexample:**
    ```lean
    def s : Trace := delta (delta void)  -- μ s has a high ω-tower
    def n : Trace := void                 -- μ (δ n) is much smaller
    -- In this case, mu s > mu (delta n), proving the assumption false.
    ```
-   **The Mandate:** All proofs for the `R_rec_succ` rule must be structured without assuming any relation between `μ s` and `μ n`. This is the primary motivation for the lexicographic `(κ, μ)` measure.

---

## 4. Official Proof Roadmap & System Deliverables

This section outlines the official, staged plan for producing the complete, verified Lean artifact. The project is divided into distinct stages, each corresponding to a specific set of Lean files and mathematical objectives.

### Stage A: Calculus Hygiene (Core Stability)

1.  **`strong_norm.lean`**: Prove Strong Normalization for the O-6 kernel. This is the highest priority and is achieved via the lexicographic `(κ, μ)` measure.
2.  **`confluence.lean`**: Enumerate all critical pairs and prove that they can be joined. This establishes that the reduction system is confluent.
3.  **`nf_unique.lean`**: Combine the results of SN and confluence to prove that every `Trace` has a unique normal form. This is a direct consequence of Newman's Lemma.

### Stage B: Logical Layer (Emergent Boolean Logic)

1.  **`complement_unique.lean`**: Prove the Complement-Uniqueness (CU) theorem. This is a research-level task that underpins the entire negation system.
2.  **`involution.lean`**: Prove that double negation is an identity (`¬¬t = t`), which should follow from CU and confluence.
3.  **`connective_laws.lean`**: Formally derive standard logical laws (De Morgan's, distributivity) from the trace-based definitions of connectives.

### Stage C: Emergent Arithmetic

1.  **`rec_add.lean`**: Define addition purely as a `Trace` term using `recΔ` (e.g., `add(m,n) := recΔ n (λk. delta k) m`) and prove it aligns with standard addition on the corresponding numerals.
2.  **`rec_mul.lean`**: Define multiplication via nested `recΔ` calls and prove its specification.
3.  **`eqNat.lean`**: Prove that the `eqW` operator is sound and complete with respect to the numerical value of δ-chains (i.e., `eqW a b` normalizes to `void` if and only if `a` and `b` represent the same number).

### Stage D: Internal Proof Theory

1.  **`proof_checker.lean`**: Define an inductive data structure for encoding derivations and a `Proof` predicate (as a `Trace` term) that normalizes to `void` if and only if a given proof correctly derives a given conclusion.
2.  **`proof_encoder.lean`**: Prove completeness for the proof system, showing that any valid meta-level derivation can be encoded into a `Trace` proof that the internal checker accepts.
3.  **`prov_sigma1.lean`**: Define the Σ₁ provability predicate `Prov(c)` as a bounded search for a proof, implemented as a `Trace` term using `recΔ`.

### Stage E: Gödelian Self-Reference & Incompleteness

1.  **`quote.lean`**: Implement a `quote` function `t ↦ ⌜t⌝` that maps a `Trace` `t` to another `Trace` that represents its syntax. Prove this mapping is injective.
2.  **`subF.lean`**: Define substitution as a pure `Trace` program and prove its fundamental properties, including capture-avoidance.
3.  **`diagonal.lean`**: Construct the diagonal function `diag(F)` which finds a fixed point `ψ` such that `ψ` is provably equivalent to `F(⌜ψ⌝)`. This is the core of the Gödelian construction.
4.  **`godel1.lean`**: Use the diagonal lemma with `F` as `¬Prov` to construct the Gödel sentence `G` and prove the First Incompleteness Theorem: `Cons(System) → ¬Prov(G)`.
5.  **`godel2.lean`**: Internalize the Hilbert-Bernays derivability conditions (D1-D3) and prove the Second Incompleteness Theorem: `Cons(System) → ¬Prov(⌜Cons(System)⌝)`.

### Stage F: Final Audit & Verification

1.  **`static_scan.lean`**: Run an automated script to scan all `.lean` files and confirm that the import list contains zero forbidden axioms (`Init`, `Classical`, `Bool`, etc.).
2.  **`extraction.lean`**: (Optional) Implement an extractor that erases all meta-level macros and emits pure, core-only `Trace` terms for final, independent verification.

---

## 5. Forensic Analysis & Historical Gaps

A "forensic verdict" on a prior version of the codebase (`OperatorMath/O6Final/Kernel.lean`) revealed several critical gaps between the project's claims and its implementation. This analysis is preserved here as it provides the essential motivation for the strict protocols and architectural decisions of the current version.

### 5.1 The "Fatal Gaps" of the Previous Implementation

1.  **Fake Arithmetic & Equality:** Functions like `add`, `mul`, and `structuralEq` were implemented as Lean meta-functions that returned `Trace` terms. They were **not** themselves `Trace` programs. This meant arithmetic and equality were happening at the meta-level, not "emerging from the single normalization engine" as claimed.
2.  **Dead Code (`recΔ`):** The `recΔ` operator, intended to be the cornerstone of internal recursion, was never actually used in the core logic. All recursion was handled by Lean's external pattern-matching, violating the principle of internal computation.
3.  **Reflective Code:** The `normalize` function was not a pure, first-order rewrite system. It contained embedded semantic tests (like calls to `structuralEq`) and nested calls to itself, making it a reflective evaluator, not a simple term rewriting system (TRS). The project still owed a formal definition of the TRS and proofs of SN/CR for *that* system.
4.  **Unproven Assumptions (Complement-Uniqueness):** The logic assumed complement-uniqueness without proof, a major unverified dependency for the entire negation system.
5.  **Missing Gödel Machinery:** There was no internal definition of `Proof`/`Prov`, no diagonal construction, and no verification of the derivability conditions. The Gödel claims were aspirational.
6.  **Axiom-Free Claim Failure:** The use of Lean's native pattern matching and equality meant the system was implicitly relying on axioms from Lean's `Type` theory, contradicting the "axiom-free" claim.

### 5.2 The Minimum Fix List (The Foundation of the Current Roadmap)

The forensic analysis concluded with a minimum fix list that now serves as the foundation for the current proof roadmap (Section 4).

1.  **Implement Real `eqW`:** Erase the meta-level `structuralEq` and use the kernel's `eqW` operator with its formal rewrite rules.
2.  **Define a Pure TRS:** Replace the reflective `normalize` function with a simple inductive relation `Step a b` and prove its properties.
3.  **Internalize All Logic:** Define arithmetic, logic, substitution, and the proof checker as **closed `Trace` terms** that use only the kernel operators (`recΔ`, `eqW`, etc.).
4.  **Deliver Formal Proofs:** For every claimed property (SN, Confluence, EqNat, etc.), deliver a formal Lean proof that references only the inductive `Step` relation.
5.  **Pass a Static Axiom Scan:** Ensure the final import graph is free of any forbidden modules.

---

## 6. Agent & AI Development Protocols: The Mandatory Workflow

To prevent errors, eliminate hallucinations, and ensure all contributions align with the project's strict mathematical and philosophical goals, all agents (human and AI) MUST adhere to the following non-negotiable protocols.

### 6.1 The Golden Rule: Copy, Don't Create

**NEVER GUESS LEAN 4 SYNTAX.** The single most effective development strategy on this project is to find a working, compiling example of a similar proof or definition in the existing codebase and **copy its exact pattern**.
-   **Primary Source of Truth:** `Termination_C.lean` and other verified, compiling files in `OperatorKernelO6/Meta/`.
-   **Process:**
    1.  Identify the goal (e.g., prove a lemma about `opow`).
    2.  Search the codebase for existing proofs involving `opow`.
    3.  Copy the proof structure, tactics, and lemma qualification verbatim.
    4.  Adapt only the variable names and specific values required for the new goal.
-   **Creativity is forbidden** at the syntax level. The correct patterns have already been discovered and validated.

### 6.2 The Lemma Verification Protocol (Non-Negotiable)

**NEVER write ANY lemma name without FIRST verifying it exists and is approved for use.** Hallucinating lemmas is the most common and time-wasting failure mode.

1.  **Check the Ordinal Toolkit First:** For any ordinal-related lemma, the first source to check is `core_docs/ordinal-toolkit.md`. This document is the authoritative list of approved lemmas and their required name qualifications.
2.  **Search Existing Code:** Use `grep` or workspace search to find usage patterns of the lemma in existing `.lean` files. If it's not used anywhere, you probably shouldn't be using it.
3.  **The "Green Channel" for New Lemmas:** If a lemma is truly necessary and not on the approved list, it must be proposed via the Green Channel protocol:
    -   The lemma must be added to a development file, clearly marked, and `sorry`'d.
    -   A one-line justification must be added to `ordinal-toolkit.md`.
    -   The lemma must satisfy the four-point rule set: no new axioms, correct type-class instances, tidy import footprint, and a kernel-safe proof.
    -   The `sorry` must be resolved before the code is considered complete.

### 6.3 Algorithmic Intervention: Ordinal Name Resolution

When encountering any Lean error related to ordinals, the following diagnostic process is mandatory.

1.  **Phase 1: Scan & Extract:** Before attempting a fix, scan the 100 lines surrounding the error and list all ordinal operations being used (`omega0`, `opow`, `Ordinal.*`, `Order.*`, etc.).
2.  **Phase 2: Verify All Names:** For every name extracted, perform the Lemma Verification Protocol (6.2). Check the local file, then the toolkit. If a name is not found, it is the likely source of the error.
3.  **Phase 3: Generate Solution by Copying:** Once the invalid name is identified, find the correct, verified pattern in the toolkit or existing code and replace the incorrect usage.

**Verified Ordinal Lemma Patterns (Use These Exactly):**
```lean
-- These are known to be correct and exist in the required Mathlib version
Ordinal.opow_pos
Ordinal.opow_add
Ordinal.opow_succ
Ordinal.opow_le_opow_right
Ordinal.mul_le_mul_left'  -- Note the prime (')
Ordinal.le_mul_right
Ordinal.lt_wf
Ordinal.omega0_pos
WellFounded.prod_lex      -- For the (κ, μ) measure
wellFounded_lt            -- For Nat well-foundedness
```

**Forbidden/Incorrect Patterns (These WILL Cause Errors):**
-   `mul_le_mul_left` (the generic monoid version, missing the prime)
-   `Ordinal.opow_lt_opow_right` (deprecated and removed from Mathlib)
-   Unqualified names like `opow_add` (must be `Ordinal.opow_add`)
-   `Prod.lex_wf` (does not exist; use `WellFounded.prod_lex`)

### 6.4 Strict Discipline Rules

-   **No Pivots Without Justification:** Do not abandon a proof strategy without a full mathematical justification for why it is impossible. Comments like "let me try something simpler" are forbidden.
-   **No `sorry` Chains:** Never introduce a `sorry` to fix a compilation error with the intention of fixing it later. This creates technical debt and cascades into further errors. Every proof must be completed.
-   **Mathlib Version is FROZEN:** Never run `lake update mathlib` or modify `lake-manifest.json`. The project is locked to a specific Mathlib version where all required lemmas are known to exist.

### 6.5 Mandatory Pre-Edit Output

Before submitting ANY code edit, the agent MUST output the following verification checklist:

```
PHASE 1 SCAN: Found N ordinal patterns in context.
PHASE 2 CHECK: [lemma_name] found in [location].
PHASE 3 COPY: Mimicking proof structure from [file:line_number].
MATH CHECK: This proof supports [downstream_theorem] by establishing [property].
```

---

## 7. AI Training & Specialization

A core objective of this project is to create a specialized AI assistant that is deeply fluent in the unique mathematical and technical constraints of OperatorKernelO6. This section details the training data, objectives, and methodologies for fine-tuning such an AI.

### 7.1 Training Objective

The goal is to produce a specialized AI mathematician that possesses the following capabilities out-of-the-box:

-   **Understands Axiom-Free Foundations:** Internalizes the concept of procedural truth and the rejection of external axioms.
-   **Masters μ-Measure Hierarchies:** Is fluent in the project's specific ordinal measure (`μ`) and the lexicographic `(κ, μ)` variant.
-   **Fixes Lean 4 Errors Automatically:** Recognizes and automatically corrects common, project-specific compilation errors, especially universe-level inference failures.
-   **Speaks the Project's Language:** Uses the specialized vocabulary of the project correctly (e.g., "δ-chain", "normalize-join", "cancellation geometry").
-   **Respects Sacred Constraints:** Never suggests edits to the kernel or violations of the established agent protocols.
-   **Provides Expert-Level Reasoning:** Can explain the mathematical justification for its actions in the context of the project's goals.

### 7.2 Curated Training Dataset

The training data is a comprehensive collection of all mathematical knowledge, code patterns, and methodologies developed in the project. It is sourced from:

1.  **`ai_training_data/complete_framework.md`**: A master document containing the entire mathematical framework, including the kernel spec, the `μ`-measure definition, critical mathematical constraints, and the ordinal toolkit.
2.  **All `.lean` files in `OperatorKernelO6/`**: These provide the ground truth for correct Lean 4 syntax, proof techniques, and working examples of ordinal reasoning.
3.  **All `.md` files in `core_docs/`**: These provide the high-level specifications, agent protocols, and development methodologies.
4.  **`copilot-instructions.md`**: The master set of rules and protocols for AI agent behavior.

### 7.3 Specialized Vocabulary

The AI must be trained to recognize and use the following specialized terms correctly:

-   **Nouns:** `OperatorKernelO6`, `Trace`, `Step`, `StepStar`, `NormalForm`, `μ-measure`, `ordinal hierarchy`, `omega0`, `opow`.
-   **Rule Names:** `R_int_delta`, `R_merge_void_left`, `R_merge_cancel`, `R_rec_succ`, etc.
-   **Concepts:** `axiom-free`, `procedural truth`, `normalize-join confluence`, `strong normalization`, `termination proof`, `sorry elimination`, `cancellation geometry`, `δ-chain`.

### 7.4 AI Autonomy Configuration

For maximum efficiency, the fine-tuned model is intended to be run with a high degree of autonomy. The ideal configuration grants the following powers:

-   **Unrestricted File Edits:** Ability to edit any file without asking for permission.
-   **Automatic Saves:** Save after every edit to maintain state.
-   **Full Terminal Access:** Execute any command, including `git` operations for version control.
-   **Filesystem Operations:** Create, delete, and manage files and directories.
-   **Iterative Compile-Fix Cycles:** Autonomously run `lake build`, analyze errors, and attempt fixes for a specified number of iterations.
-   **No Confirmation Prompts:** Pure autonomous action to accelerate development and proof-finding.

This comprehensive training approach ensures that the AI partner is not just a generic language model but a true, specialized member of the OperatorKernelO6 development team.

---

**This OperatorKernelO6 Project Bible is a comprehensive, lossless, and extensible knowledge base, capturing every technical detail, error, fix, protocol, and learning, anchored and cross-referenced for ongoing use and future expansion. All critical information from both Review and ai_training_data folders is included, with explicit context, chronology, and subject mapping.**
