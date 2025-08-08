Checklist (what you asked)

- Full comprehensive project status, including math framework and important details
- Explain which tactics/approaches didn’t work and why

Project status (code, build, blockers)

- Toolchain and project
	- Lean 4.22.0-rc4 with mathlib; Lake builds via “Lean build”.
	- Workspace: Termination_C.lean is the active file; you manually edited it recently (an “end MetaSN” was appended via PowerShell).
- Build
	- Build fails in OperatorKernelO6.Meta.Termination_C.lean with first errors in:
		- The both-void eq_diff proof block (incorrect goal-shape around succ/+n and a product collapse rewrite that wasn’t fully propagated).
		- κ obligations (kappa = 0) for non-rec traces left as unsolved goals in several branches.
		- Misused ordinal monotonicity instances (attempts to use non-existent AddRightStrictMono on Ordinal).
	- There are also “sorry”s remaining:
		- Termination.lean:906 (pre-existing).
		- One local sorry in Termination_C around 1354–1359 (shifted by edits; still present).
- What’s implemented and stable
	- Measures:
		- μ (ordinal) for Trace with constructors:
			- void = 0
			- delta t = ω^5 · (μ t + 1) + 1
			- integrate t = ω^4 · (μ t + 1) + 1
			- merge a b = ω^3 · (μ a + 1) + ω^2 · (μ b + 1) + 1
			- recΔ b s n = ω^(μ n + μ s + 6) + ω · (μ b + 1) + 1
			- eqW a b = ω^(μ a + μ b + 9) + 1
		- κ (Nat) nests only on the third argument of recΔ; 0 elsewhere. Lemma kappa_non_rec provided.
		- μκ := (κ, μ) with lex order; wf proved via product lex wf.
	- Ordinal toolkit (SSOT-safe)
		- Strict monotonicity of ω^• in exponent: isNormal.opow → opow_lt_opow_right/opow_le_opow_right.
		- “+1 bridges”: lt_add_one_of_le, add_one_le_of_lt, add1_lt_add1, le_of_lt_add_one for shaping goals that add 1.
		- Principal add: principal_add_omega0_opow κ to bound finite sums under ω^κ (used at κ=3 and κ=4).
		- Finite absorption when ω ≤ p: nat_left_add_absorb and one_left_add_absorb (with case split for finite vs infinite).
		- Safe multiplicative monotonicity: mul_lt_mul_of_pos_left, mul_le_mul_left'/right' with explicit positivity.
	- Constructor μ-increase lemmas:
		- mu_lt_delta, mu_lt_merge_void_left/right, mu_lt_merge_cancel, mu_lt_rec_zero.
	- Merge payload bounds:
		- termA_le (ω^3*(x+1) ≤ ω^(x+4)), termB_le (ω^2*(x+1) ≤ ω^(x+3)).
		- payload_bound_merge and payload_bound_merge_mu.
	- A-structure for recΔ comparisons:
		- w3_lt_A, coeff_lt_A, head_lt_A, tail_lt_A scaffolding (with a parameterized hypothesis on the dominating A).
	- Merge inner bound and eq_diff (general):
		- merge_inner_bound_simple shows μ(merge a b) + 1 < ω^(μ a + μ b + 5).
		- mu_lt_eq_diff lifts through integrate to ω^(μ a + μ b + 9) then “+1 bridge” compares to eqW; uses finite absorption except both-void.

The both-void eq_diff special case: current proof and issues

- Goal: μ(integrate (merge void void)) < μ(eqW void void).
- Our normalized target:
	- LHS as ω^4 · (ω^3 + ω^2 + 2) + 1
	- RHS as ω^9 + 1
- Structure of the proof (correct SSOT plan):
	1. Show inner (ω^3 + ω^2 + 2) < ω^4:
		- Use principal_add at κ=3 to get ω^2 + 2 < ω^3 (needs ω^2 < ω^3 and 2 < ω^3).
		- Then principal_add at κ=4: ω^3 + (ω^2 + 2) < ω^4.
	2. Multiply by ω^4 and collapse ω^4·ω^4 to ω^8 via opow_add with base ω.
	3. Bump ω^8 < ω^9 and lift across +1 to reach ω^9 + 1.
- What’s still wrong (first errors):
	- A lingering equality/shape expectation in this region uses successors: expects ω^4 * (ω^3 + succ (succ ω^2)) instead of ω^4 * (ω^3 + ω^2 + 2). We attempted to avoid succ_succ; however, some simp/goal still expects the succ form. This causes simpa/type-mismatch failures in the final “simpa [mu] using …” lines.
	- A rewrite to collapse ω^4ω^4 to ω^8 was added (using (opow_add …).symm), but a preceding step still asserts “< ω^4 * ω^4” instead of “< ω^8”; Lean wants that rewrite applied before the comparison. Currently, the proof has h_prod: … < ω^4ω^4; then later a h_collapse equation; but the “simpa using” needs the rewrite already in place for typeclass resolution. This leaves a type mismatch.
	- A few earlier attempts reintroduced succ_succ in simp; removing it fixed one set of errors but created mismatches where the local goal still expects Order.succ forms. We need to normalize consistently (either all in +n or in succ) in that block.

κ obligations and recΔ branches (open goals)

- Unsolved κ goals:
	- Repeated ⊢ kappa b = 0 in non-rec branches at multiple points (~1300-line range).
	- Fix: case-split and apply kappa_non_rec; do not use contradiction. In recΔ cases, κ is non-zero by definition; in all others, κ=0 is by cases/simp.
- ‘contradiction’ failures in recΔ cases:
	- Tactic was used without contradictory hypotheses; there isn’t a direct False derivation.
	- Fix: explicitly use the μ-increase/decrease lemmas to derive a strict inequality chain rather than contradiction, or split cases and discharge with κ-drop on recursive steps.

Mathematical framework recap (SSOT)

- Single Source of Truth for ordinal bounds:
	- ω-power strict monotonicity in exponents: opow_lt_opow_right / opow_le_opow_right (base = ω).
	- Principal-add bounding is the workhorse for finite sums under a single ω^κ ceiling.
	- +1 bridges to move between X < Y and X+1 ≤ Y (and the reverse).
	- Finite absorption: when ω ≤ p, (n : Ord) + p = p; needed when lifting integrate/merge payloads into higher towers.
	- Multiplication monotonicity is done only with explicit positivity witnesses.
- Termination lex measure:
	- Primary: κ (nesting of recΔ on the third argument); Secondary: μ (ordinal height).
	- For non-rec constructors, κ = 0; for recΔ it increases by nesting; proofs should combine μ decreases with κ drops for well-founded recursion.

What did not work (and why)

- Relying on strict monotonicity of ordinal addition on the right:
	- Attempted to use AddRightStrictMono Ordinal (not available). Ordinal addition is not strictly monotone in the right argument in general. This caused “failed to synthesize AddRightStrictMono” errors.
	- Fix used: “+1 bridges” (Order.add_one_le_of_lt, lt_add_one_of_le, le_of_lt_add_one) and principal_add instead of generic add monotonicity.
- Using ring-like lemmas on ordinals (three_mul, two_mul, arithmetic simp):
	- Ordinal arithmetic isn’t commutative/associative in the same way as ℕ/ℤ under standard ring rules; the “three_mul” rewrite was unknown and invalid here; also “simp made no progress” often occurs with such guesses.
	- Fix used: derive the exact ordinal multiplication chains via mul_succ, explicit recasting with set a := ω^(x+4), and equalities like a*3 = a + (a + a).
- Wrong opow_pos usage (type mismatch “expected Type, got Prop”):
	- opow_pos needs arguments in the correct named-parameter order: Ordinal.opow_pos (a := omega0) (b := exponent) omega0_pos. Passing omega0_pos directly without naming caused type mismatch.
	- Fix used: always pass named args and/or use helper lemmas opow_lt_opow_right/opow_le_opow_right that wrap positivity internally.
- succ vs +n shape mismatches:
	- Swapping between Order.succ layers and +1/+2 expressions in lhs/rhs goals caused simpa to fail or expect different forms. The both-void lemma drifted between forms, causing repeated mismatches.
	- Fix in-progress: pick one convention (prefer +n), rewrite consistently in the block, and avoid succ_succ unless the goal is already in succ form (or rewrite both sides to the same shape before simpa).
- Using “contradiction” in recΔ branches:
	- There wasn’t an explicit p ∧ ¬p to discharge. Needs a structured inequality argument via μ/κ rather than contradiction.
- Assuming right-additive strict monotonicity to lift inequalities through + on the right:
	- Not valid for ordinals in general; replaced by principal_add with ω^κ ceilings and +1 bridges.
- Using Nat lemmas not in scope (Nat.succ_pos_iff, Nat.zero_lt_succ_iff) and undefined names (hκ):
	- Lean flagged unknown constants and identifiers. Use Nat.succ_pos k or Nat.pos_of_gt and keep consistent notation; bind names earlier or avoid phantom identifiers.

Immediate next steps (surgical fixes)

- Both-void lemma
	- Normalize all occurrences to +n forms:
		- Replace any lingering Order.succ (Order.succ (…)) expectations by rewriting to +2 on both sides of the equality before the final simpa.
	- Push the ω^4·ω^4 → ω^8 rewrite earlier:
		- After obtaining h_prod: ω^4 * (…) < ω^4 * ω^4, immediately rewrite RHS via (opow_add …).symm and change the statement to < ω^8, so the subsequent trans and simpa see exactly ω^8.
	- Ensure opow_pos/opow_lt_opow_right are used with named args to avoid type errors.
	- Final step: apply add_one bridge once (lt_add_one_of_le ∘ add_one_le_of_lt) to go from inner strict bound to the +1 inequality with the target ω^9 + 1.
- κ obligations (non-rec)
	- Where goals show ⊢ kappa t = 0 with t not recΔ, do cases t; simp [kappa] or use kappa_non_rec with a brief non-exists witness; do not use contradiction.
- recΔ contradiction blocks
	- Replace “contradiction” with an explicit argument:
		- Either show μ terms compare the wrong way using mu_merge/rec lemmas, or case-split to non-rec and apply κ drop in the lex order proof rather than contradiction.
- Clean unused simp args and unknown identifiers
	- Remove unused simp args flagged by linter (add_comm, add_left_comm, one_mul, add_zero in those simp calls).
	- Replace Nat.succ_pos_iff/zero_lt_succ_iff with Nat.succ_pos or (Nat.succ_pos n) and use Nat.cast lemmas already imported.

Quality gates (current)

- Build: FAIL (OperatorKernelO6.Meta.Termination_C).
- Lint/Typecheck: Multiple errors, plus linter warnings for unused simp arguments.
- Tests: None present in repo; not applicable.
- Smoke checks: N/A.
Requirements coverage: Report requested (Done). Tactics/approaches that failed explained (Done).


Notes and guidance

- Keep to SSOT: principal_add for sum ceilings, opow monotonicity, +1 bridges, explicit positivity for mul, avoid right-add monotonicity assumptions.
- For both-void, we cannot rely on “ω ≤ μ a + μ b” absorption (C=0); that’s why the explicit κ=3 and κ=4 principal-add steps are necessary before the ω^4 multiplication and exponent bump.
If you want, I can apply the both-void block cleanup (consistent +n forms, early ω^8 rewrite) and then tackle the κ=0 obligations right after, then rebuild and iterate on the first new error.


Plan


Plan at a glance

- Lock the measure and toolset.
- Close both-void eq_diff cleanly (normalize goal-shapes, early ω^8 rewrite).
- Discharge κ=0 obligations by cases; remove “contradiction” from recΔ blocks.
- Prove μκ-decrease for all 8 rules; assemble WellFounded.
- Keep normalize-join scaffolding ready for confluence.

Targets and “contract”

- Inputs: Trace constructors and Step rules (8 rules).
- Output: For each Step t u, μκ u < μκ t (lex on (κ, μ)).
- Error modes: succ vs +n shape mismatches; misuse of right-add monotonicity; missing κ=0; opow_pos arg order; unknown algebraic rewrites.
- Success: lake build passes; no sorry; μκ-decrease per rule; WF via InvImage.wf/Prod.Lex; both-void and general eq_diff hold.

Core setup (measures + toolkit)

- Measures (fixed):
	- κ: kappa (Nat), counts nesting on recΔ’s third arg only; κ=succ (κ n) for recΔ; κ=0 for others.
	- μ: Ordinal.{0} height:
		- void = 0
		- delta t = ω^5 · (μ t + 1) + 1
		- integrate t = ω^4 · (μ t + 1) + 1
		- merge a b = ω^3 · (μ a + 1) + ω^2 · (μ b + 1) + 1
		- recΔ b s n = ω^(μ n + μ s + 6) + ω · (μ b + 1) + 1
		- eqW a b = ω^(μ a + μ b + 9) + 1
	- μκ := (κ, μ) with Prod.Lex Nat.lt Ordinal.lt; wf via product_lex well-foundedness.
- Ordinal toolkit (only these):
	- opow strict/weak mono: opow_lt_opow_right, Ordinal.opow_le_opow_right (a := omega0).
	- “+1 bridges”: Order.add_one_le_of_lt, Order.lt_add_one_iff; lt_add_one_of_le; add1_lt_add1.
	- Principal-add ceiling: Ordinal.principal_add_omega0_opow κ for α+β<ω^κ (and 3-sum via two calls).
	- Finite absorption: one_add_of_omega0_le, natCast_add_of_omega0_le; use only when ω ≤ p.
	- Safe mul mono: Ordinal.mul_lt_mul_of_pos_left, mul_le_mul_left'/right' with explicit 0<left factor.
	- Rewrite ω^a · ω^b to ω^(a+b): via (opow_add …).symm; use named args; avoid ring-like rewrites.

Rule-by-rule μκ-decrease

- R_int_delta: integrate (delta t) → void
	- κ: 0 → 0; μ: μ void = 0 < μ(integrate (delta t)) by simp [μ]; done.
- R_merge_void_left/right: merge void t → t; merge t void → t
	- κ: 0 → 0; μ: use mu_lt_merge_void_left/right already present; done.
- R_merge_cancel: merge t t → t
	- κ: 0 → 0; μ: mu_lt_merge_cancel; done.
- R_rec_zero: recΔ b s void → b
	- κ: succ κ(void) → 0 (strict drop); lex-win even if μ grows; also mu_lt_rec_zero gives μ b < μ recΔ; done.
- R_rec_succ: recΔ b s (delta n) → merge s (recΔ b s n)
	- κ: LHS κ = succ (κ (delta n)) > 0; RHS top constructor is merge → κ=0; strict drop; no μ needed.
- R_eq_refl: eqW a a → void
	- κ: 0 → 0; μ: mu_void_lt_eq_refl; done.
- R_eq_diff: eqW a b → integrate (merge a b)
	- General a,b:
		- Inner bound: μ(merge a b) + 1 < ω^(μ a + μ b + 5) via termA_le + termB_le + payload_bound_merge(mu a).
		- Lift integrate: ω^4 · (…)+1 ≤ ω^(μ a+μ b+9) using Ordinal.opow_le_opow_right on exponents (add4_plus5_le_plus9) and “+1 bridge”.
		- If ω ≤ μ a + μ b (not both void), finite absorption is safe when needed; conclude μ(integrate (merge a b)) < μ(eqW a b).
	- Special both-void:
		- Normalize both sides to +n (no succ): LHS = ω^4 · (ω^3 + ω^2 + 2) + 1; RHS = ω^9 + 1.
		- Show ω^3 + ω^2 + 2 < ω^4:
			- ω^2<ω^3 and 2<ω^3; principal_add@3 ⇒ ω^2+2 < ω^3.
			- principal_add@4 ⇒ ω^3 + (ω^2+2) < ω^4; reassociate to ω^3+ω^2+2.
		- Multiply by ω^4 on the left with positivity; immediately rewrite RHS:
			- h_prod: ω^4 · (…) < ω^4 · ω^4; then rewrite ω^4 · ω^4 to ω^8 via (opow_add …).symm at this step so the inequality is < ω^8 (no dangling “· ω^4”).
		- Bump ω^8 < ω^9; chain inequalities; lift across +1 using Order.add_one_le_of_lt then lt_add_one_of_le; conclude ω^4 · (…) + 1 < ω^9 + 1.

Precise fixes for current failures

- Both-void region:
	- Remove any succ_succ references; rewrite all succ(succ x) to x+2 or rewrite the goal to +2 before using simpa.
	- Apply the ω^4·ω^4 → ω^8 rewrite directly in the proof of that strict inequality (not later) so the target matches ω^8 in the next line.
	- Use named args for opow_pos/opow_* monotone calls to avoid “expected Type, got Prop”.
- κ obligations:
	- When Lean asks ⊢ kappa b = 0 (non-rec branches), do “cases b” and simp [kappa] or apply kappa_non_rec with a trivial non-existence witness; do not use contradiction.
- recΔ “contradiction”:
	- Replace with explicit lex decrease: show κ drops from succ … to 0 for the successor rule; for zero case, use μ b < μ recΔ; no contradiction tactic needed.
- Clean linter noise:
	- Remove unused simp args (add_comm, add_left_comm, add_zero, one_mul) in the impacted proofs.
	- Replace Nat.succ_pos_iff/zero_lt_succ_iff with Nat.succ_pos n and already-imported Nat.cast lemmas.

Edge cases to guard

- Finite vs infinite splits: use eq_nat_or_omega0_le when deciding absorption; never assume ω ≤ μ a + μ b for both-void.
- Do not use right-add strict monotonicity on ordinals; always go via principal_add ceilings or +1 bridges.
- Keep μ s vs μ (delta n) unrelated in recΔ proofs (they’re independent).

Minimal test harness (mental smoke)

- Both-void: check the chain yields “< ω^8” before bump; final LHS/RHS shapes are “+ 1” on both sides.
- κ drops: ensure all merge-target RHS have κ=0 by definition.

Tactics guide

- Prefer: simp [μ, …], exact, calc with named lemmas; opow_* with named args; principal_add_omega0_opow; add_one bridges; mul_le_mul_left'/right'; Ordinal.mul_lt_mul_of_pos_left; (opow_add …).symm for product collapse.
- Avoid: generic right-add strict monotonicity, ring-like rewrites (three_mul), contradiction in non-contradictory branches, unqualified opow_pos calls, succ_succ inside mixed +n goals.