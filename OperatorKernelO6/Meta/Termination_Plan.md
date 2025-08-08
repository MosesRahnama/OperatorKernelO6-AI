Here’s a precise, SSOT-compliant diagnostic before any more edits, plus a concise report of what changed in this file so far.

Checklist
Full diagnostic of current build errors and root causes
SSOT PHASE 1/2/3 verification on ordinal lemmas
Exact list of edits already made (delta)
Targeted, ordered fix plan (first-error-first)
Current build status (from last lake build)
Top blocking errors in OperatorKernelO6/Meta/Termination_C.lean:

Helper lemma kappa_non_rec — recΔ case doesn’t close
Location: line ~77
Error: unsolved goals under case recΔ … ⊢ False
Root cause: The proof cases t <;> intro _ <;> simp [kappa] doesn’t handle the recΔ contradiction; for t = recΔ …, the premise is false, but we never turn it into False to discharge the goal.
Helper lemma add1_lt_add1 — type mismatch chain
Location: lines ~83–86
Error: a + 1 ≤ b mismatch where goal is a + 1 ≤ b + 1; also lt_of_le_of_lt receives b < b + 1 but expects b + 1 < b + 1
Root cause: Using Order.add_one_le_of_lt to build a ≤ chain then lt_of_le_of_lt is the wrong shape. The correct lemma is Ordinal.add_lt_add_right h 1 (or left variant with simp).
mu_lt_eq_diff_both_void — multiple ordinal arithmetic issues
Location: lines ~246–307 (the “step1–step4” block)
Errors:
Wrong usage of local opow_lt_opow_right: given one argument (h : b < c), but code passes two args
Unknown identifier three_mul
“AddRightStrictMono Ordinal” synthesis failure (red-flagged in toolkit)
opow_pos called with wrong argument order
Goal shape mismatch to Order.succ rewrites when simp introduces succs
Root causes:
Nonexistent/forbidden lemma names (three_mul; AddRightStrictMono)
Misusing local opow_lt_opow_right (it accepts a single < proof)
opow_pos signature mismatch (needs base positivity; use named args)
Relying on ordinal equalities like 3·ω^3 = ω^3+ω^3+ω^3 that aren’t in the toolkit and are brittle
μκ_decreases — three contradiction failures and κ=0 subgoals
Locations: lines ~1282, 1297, 1301, 1305, 1372, 1378, 1384
Errors: contradiction fails in recΔ branches; subgoals requesting kappa … = 0
Root cause: using contradiction on a b : Trace that could be recΔ; need a helper: kappa_non_rec or kappa_eq_zero_of_not_rec to explicitly discharge κ=0 for non-rec traces and avoid contradiction for recΔ
mu_decreases — last sorry in R_rec_succ
Location: lines ~1359
Error: one remaining sorry guard (although we replaced it in later edits)
Root cause: that branch must use the available lexicographic drop μκ_lt_R_rec_succ; the μ proof then follows by case split
Note: There’s a warning about a different file using sorry (OperatorKernelO6/Meta/Termination.lean:906). That’s out of this file’s scope.

SSOT checks (mandatory)
PHASE 1 SCAN: extracted ordinal patterns used around the failing regions

Exponentiation: opow, opow_add, local opow_lt_opow_right, (expected) Ordinal.opow_le_opow_right
Positivity: omega0_pos, opow_pos
Multiplication monotone (left): Ordinal.mul_lt_mul_of_pos_left
Addition monotone: add_lt_add_left, add_lt_add_of_lt_of_le (amber), add_lt_add_right (allowed per toolkit 2.2)
Successor bridge: Order.lt_add_one_iff, Order.add_one_le_of_lt
Principal ordinals: Ordinal.principal_add_omega0_opow (imported module is present)
PHASE 2 CHECK: lemma names vs toolkit

Allowed and present: Ordinal.mul_lt_mul_of_pos_left, opow_add, Order.add_one_le_of_lt, add_lt_add_left, add_lt_add_right (listed in 2.2), nat_lt_omega0, one_lt_omega0, omega0_pos
Local: opow_lt_opow_right (we defined it at top; single-argument signature)
Red/Forbidden/not in toolkit: three_mul (unknown), AddRightStrictMono tactic need (avoid), generic mul_le_mul_left (forbidden for ordinals)
Existence confirmed in repo/imports; no new axioms
PHASE 3 COPY: proof structure to mimic

Use additive-principal ω^κ sums (Ordinal.principal_add_omega0_opow) to bound ω^3 + ω^2 + 2 < ω^3 (all summands < ω^3)
Then lift inequalities via Ordinal.mul_lt_mul_of_pos_left with positive left factor ω^4
Use opow_add to rewrite ω^4 * ω^3 = ω^7, then strict exponent growth to reach ω^9
For +1 lift: use Ordinal.add_lt_add_right main_bound 1 (or the tiny helper add1_lt_add1 implemented correctly)
What I changed in this file (delta)
Imports: Mathlib.SetTheory.Ordinal.Principal already present (kept)
Inserted helper lemmas just after kappa:
kappa_non_rec (currently too naive for recΔ; needs short exfalso)
add1_lt_add1 (current proof uses Order.add_one_le_of_lt; it should be replaced with Ordinal.add_lt_add_right)
Rewrote mu_lt_eq_diff_both_void to the “step1–step4” structured version
Replaced R_merge_* cases in μκ_decreases to a κ-aware by_cases version that falls back to Prod.Lex.left when κ drops
Replaced R_rec_succ branch in mu_decreases to use μκ_lt_R_rec_succ and extract μ-drop from the lex decrease
No kernel edits. No changes outside this file.

Root-cause analysis per error cluster and precise fixes
kappa_non_rec recΔ hole
Cause: For t = recΔ…, the premise ¬∃… is false; current proof doesn’t produce False
Fix: In the recΔ case, after intro h, do exact (h ⟨,,_, rfl⟩).elim to get False, then close goal by exact (by cases False.elim with …). Concretely: cases t with | recΔ b s n => intro h; cases h ⟨b, s, n, rfl⟩ | _ => intro _; simp [kappa]
add1_lt_add1 type mismatch
Cause: wrong shape of inequalities
Fix: Replace body with: lemma add1_lt_add1 {a b} (h : a < b) : a + 1 < b + 1 := by simpa using Ordinal.add_lt_add_right h 1
mu_lt_eq_diff_both_void arithmetic
Causes and replacements:
opow_lt_opow_right: call our local lemma with a single argument (e.g., opow_lt_opow_right (by norm_num) is wrong; need a proof like (2:Ordinal) < (3:Ordinal), then “simpa” around if needed)
opow_pos: use named args per toolkit pattern: Ordinal.opow_pos (a := omega0) (b := …) (a0 := omega0_pos)
Avoid three_mul: not available and fragile for ordinals
Avoid AddRightStrictMono: not applicable
Succ vs +1: use Order.lt_add_one_iff or keep goals in +1 form; for the final lift, use add1_lt_add1 or Ordinal.add_lt_add_right
Better step1 (toolkit pattern):
Show ω^2 < ω^3 and 2 < ω^3; by principal_add_omega0_opow (κ := 3), any finite sum of < ω^3 stays < ω^3 ⇒ ω^3 + ω^2 + 2 < ω^3 is false because ω^3 + … ≥ ω^3. So we need the “sum bounded by a multiple” approach avoided. The robust path:
Show ω^3 + ω^2 + 2 < ω^3 + ω^3 + ω^3 using add_lt_add_left h₁ and add_lt_add_of_lt_of_le; but don’t turn that into 3·ω^3; it’s enough for the later left-multiplication step:
Directly apply Ordinal.mul_lt_mul_of_pos_left with c = ω^4 to both sides. No need to rewrite to 3·ω^7.
Then bound ω^4*(ω^3 + ω^3 + ω^3) < ω^4ω^3something ≤ ω^8 or go simpler:
Chain: ω^4*(ω^3 + ω^2 + 2) < ω^4*(ω^3 + ω^3 + ω^3) < ω^4*(ω^3 + ω^3 + ω^3 + ω^3) = ω^4* (4·ω^3) ≤ ω^8 (using opow_add + product monotonicity per toolkit). But to keep within SSOT, the recommended robust approach is:
Avoid coefficients entirely: instead show ω^3 + ω^2 + 2 < ω^4 (true) then ω^4 * (…) < ω^4 * ω^4 = ω^8 < ω^9. However “ω^3 + ω^2 + 2 < ω^4” is immediate by base-ω exponent strict mono: ω^3 < ω^4, ω^2 < ω^4, 2 < ω^4, and ω^4 is additive principal (so finite sum of < ω^4 is < ω^4). This uses Ordinal.principal_add_omega0_opow 4, which we already import.
That yields a clean chain with fewer moving parts and no 3·… equalities.
μκ_decreases contradictions/κ=0 subgoals
Cause: Using contradiction in recΔ branches and assuming κ b = 0
Fix: Replace contradiction with kappa_non_rec (fixed as above) where applicable; in the by_cases branches for merge, we already implemented the κ-aware path; make sure those earlier κ=0 subgoals are no longer referenced.
mu_decreases R_rec_succ
Cause: leftover sorry
Fix: The replacement using μκ_lt_R_rec_succ is correct; but extracting μ from a κ drop requires care. If the lex result is in the first component (κ), we can’t directly conclude μ-drop; instead, keep μ_decreases delegating to μκ_decreases followed by a projection — or keep the lex theorem as the final result for the lex proof, and for μ_decreases rely only on rules where μ actually drops. If the project requires μ drop for R_rec_succ, you either:
keep μκ_decreases as the main measure, or
provide a separate μ bound established elsewhere. Given the provided snippet, your current version tries to force μ from κ, which won’t type-check; prefer to keep μκ_decreases as the primary theorem.
Minimal, ordered fix plan (first-error-only)
Fix kappa_non_rec (recΔ case): exfalso with witness to close the false premise.
Replace add1_lt_add1 with Ordinal.add_lt_add_right h 1 (single line).
Rework mu_lt_eq_diff_both_void to avoid three_mul, AddRightStrictMono, and fix opow_* calls:
Use principal_add_omega0_opow (κ := 4) to show ω^3 + ω^2 + 2 < ω^4
Use Ordinal.mul_lt_mul_of_pos_left (left factor ω^4 positive)
Rewrite ω^4 * ω^4 to ω^8 via opow_add; then ω^8 < ω^9 via local opow_lt_opow_right
Final lift via add1_lt_add1
Remove residual κ=0 subgoals in merge branches by relying on the by_cases we inserted and the fixed helper.
Ensure mu_decreases R_rec_succ matches the lex approach (or defer μ for that rule and keep it in μκ theorem only, per your Measure choice).
What this supports downstream
Closes the equality-difference case needed by μ-decrease for R_eq_diff (used elsewhere at line ~1244).
Removes fragile ordinal algebra while staying within the toolkit (principal ordinals, opow_add, product monotone).
Keeps merge and rec-succ measure handling consistent with the lex measure strategy.
If you want me to proceed, I’ll implement the three surgical fixes above (kappa_non_rec, add1_lt_add1, rewrite of mu_lt_eq_diff_both_void) in-place, then run a build and iterate from the first remaining error.