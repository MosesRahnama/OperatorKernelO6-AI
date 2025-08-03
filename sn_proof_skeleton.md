# Strong Normalization (SN) Proof Skeleton and Next Steps

This document lays out the **complete skeleton roadmap** from the current state (with the core of `mu`, `mu_lt_eq_diff`, etc.) to a finalized, fully justified Strong Normalization theorem. No technical Lean code beyond names is included; instead the plan lists all required components, dependencies, case splits, and verification checks to get to the end.

---

## I. High-Level Goal
Prove that the step relation `KernelStep` (or general `R`) is well-founded by showing a decreasing measure `mu` such that every allowed reduction decreases `mu`. Then conclude Strong Normalization via the `InvImage.wf` machinery.

Formally:
- Show `∀ {a b : Trace}, KernelStep a b → mu b < mu a` (the `mu_decreases` lemma).  
- Conclude `WellFounded (StepRev KernelStep)` and/or `WellFounded KernelStep` depending on direction using `InvImage.wf` and appropriate subrelation arguments.

---

## II. Core Building Blocks (some are already green or in base)
1. **Measure `mu : Trace → Ordinal`** (defined recursively over traces) — already present and universe-consistent.  
2. **Basic ordinal arithmetic lemmas:** monotonicity, absorption, successor, limit behavior, `omega_pow_add3_lt`, `opow_lt_opow_right`, etc. These live in the base (`TerminationBase.lean`), `ordinal-toolkit.md` patterns, or `Additive_Principal_Ordinals.txt` theory.  
3. **Corner case handling helpers:** (e.g., `nonvoid_mu_ge_omega`, `mu_sum_ge_omega_of_not_both_void`) to get lower bounds like `ω ≤ mu a + mu b` when needed.  
4. **Key sub-inequalities:** the critical lemmas such as `merge_inner_bound_simple`, `mu_lt_eq_diff_both_void`, and the total `mu_lt_eq_diff`.  
5. **Chain of inequalities for each kernel rule:** for each constructor of the Step relation, a separate lemma showing a strict decrease (some already coded: `mu_lt_merge_void_left`, etc.).  

---

## III. Detailed Skeleton / Steps to Finish the SN Proof

### 1. Finalize the remaining measure-decrease lemmas (local termination inequalities)
These must be fully proven without `sorry`, with each substep broken out so failing bits localize.

- **`merge_inner_bound_simple (a b)`**: done in existing plan; shows `mu (merge a b) + 1 < ω^(C+5)` for C = μa+μb.  
- **`mu_lt_eq_diff_both_void`**: numerical corner case for `(void, void)`; show `mu(integrate(merge void void)) < mu(eqW void void)` via explicit bounds.  
- **`mu_lt_eq_diff`**: total lemma that handles both the corner and general cases, uses absorption `4 + C = C` when `ω ≤ C`.  

*After those:* all three of the previously red lemmas become green.  

### 2. Verify (or complete if missing) other intermediate lemmas used in `mu_lt_eq_diff`:
- `nonvoid_mu_ge_omega` and `mu_sum_ge_omega_of_not_both_void` (to supply the hypothesis `ω ≤ C` when not both void).  
- `nat_left_add_absorb` usage correctness: ensure its preconditions (`ω ≤ C`) satisfied and that it’s used to absorb the finite 4 into C cleanly.  

### 3. Assemble `mu_decreases` (the global decreasing measure lemma)
- Case analysis over each step constructor of the kernel relation.  
- Use the existing lemmas (e.g., `mu_lt_merge_void_left`, `mu_lt_merge_cancel`, `mu_lt_rec_zero`, `mu_lt_rec_succ`, `mu_lt_eq_diff`) to dispatch each branch.  
- Ensure each branch compiles and that there are no hidden `sorry`s leaking in.  

### 4. Well-Foundedness conclusions
Two variants depending on direction needed:
- **Forward trace**: Build `WellFounded (StepRev KernelStep)` by showing `StepRev` is a subrelation of `fun x y => mu x < mu y` and apply `InvImage.wf`.  
- **Backward version**: Similarly show `WellFounded KernelStep` if needed.  
- Use existing wrappers like `strong_normalization_forward_trace` and `strong_normalization_backward`.  

### 5. Top-Level Theorem (`step_strong_normalization`)
- Instantiate the generic theorem with `KernelStep` and the proven `mu_decreases` to get final strong normalization property on traces.  

---

## IV. Validation, Robustness & Edge Cases
1. **Totality and corner cases:** Ensure every combination of input (e.g., `void` patterns) is covered, without hidden assumptions.  
2. **No hidden dependencies:** Every lemma used must be in the green base or documented in the toolkit; avoid introducing new opaque axioms or non-whitelisted imports.  
3. **Explicit named `have` chain:** Each critical inequality should have a named `have` with a clear statement so if any proof step breaks in refactoring it’s easy to search analogous patterns in the working base.  
4. **Universe consistency:** Keep `mu : Trace → Ordinal.{0}` and avoid accidental lifting unless intentional (no new universe polymorphism unless accounted for).  
5. **Diagnostic readiness:** Keep the structure so that if a diagnostics API wants to capture failing steps, each `have` is granular (e.g., `h_head_lt`, `h_tail_lt`, `h_combined`, etc.).  

---

## V. Optional Extensions / Hardening
- Generalize to new constructors: if `Trace` grows, factor the `nonvoid_mu_ge_omega` and related exhaustion to be generically derivable (e.g., via a small automation or helper macro).  
- Extract common patterns (e.g., combining finite + ω-power bounds) into reusable helper lemmas with precise names for reuse elsewhere.  
- Add trimmed diagnostics flags locally in problematic proofs to avoid overwhelming output in CI while preserving enough evidence for failure modes.  

---

## VI. Immediate Tactical Checklist for Implementation Team
1. Copy the plan for `merge_inner_bound_simple` into Lean and confirm it matches the working lemma names.  
2. Flesh out `mu_lt_eq_diff_both_void` and verify the numeric bounds strictly hold.  
3. Complete `mu_lt_eq_diff`, ensuring the case split and absorption are clean.  
4. Rebuild and inspect `mu_decreases`; fix any newly surfaced tiny gaps (e.g., required minor lemmas used there).  
5. Run full `lake build` with diagnostics on the key region to ensure no lingering `sorry`s and to capture performance.  
6. Finalize the strong normalization theorems using the now fully proven decrease measure.  

---

If you want, I can now help you convert this skeleton into a **Lean proof template with placeholders** (only after you say so), or we can move to the next local lemma you want to un-sorry. Which direction do you want to take next?

