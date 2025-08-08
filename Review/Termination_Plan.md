# 🔧  Meta-level Strong-Normalization Cookbook  
This file is **pure comments**.  Every unfinished lemma in `Termination_C.lean` is
listed once, followed by an *assembly script* – a numbered sequence of micro-steps
that a trivial “dumb” agent can follow without creativity.

---

## Legend

• “copy-pattern X:Y”  = duplicate the proof fragment that sits in file `X`
  around line `Y` (only rename variables).  
• `tools/ordinal-toolkit.md §n`  = lemma is guaranteed to exist there.  
• “`ring`/`linarith`” = allowed tactics.  
• NEVER use a lemma before SEARCH confirms it exists.  
• All inequalities are on ordinals; keep the qualified names exactly as shown
  (`Ordinal.mul_le_mul_left'`, `Order.lt_add_one_iff`, …).

---

## 1  `wf_LexNatOrd`

1. `open Prod` and `open Lex`.  
2. `have := WellFounded.prod_lex wellFounded_lt Ordinal.lt_wf`.  
3. `simpa [LexNatOrd] using this`.

> copy-pattern: `Init/WF` lines ~120 (“prod_lex” demo).

---

## 2  `μ_to_μκ`

Goal: lift a strict μ-drop to the lexicographic order when κ is unchanged.

1. `intro t t' hμ hκ`.  
2. `unfold LexNatOrd μκ` then `rw [hκ]`.  
3. `apply Prod.Lex.right; exact hμ`.

> identical to proof for merge-void case; copy-pattern Termination_C.lean
> around the first use of `μ_to_μκ`.

---

## 3  `μκ_lt_R_rec_succ`

κ drops from `k.succ` to `k`, μ is unchanged.

1. `intro b s n`.  
2. `unfold LexNatOrd μκ`; `apply Prod.Lex.left`.  
3. `simp [kappa]`.

---

## 4  `mu_recΔ_plus_3_lt`

Parameterised helper; keep the external hypothesis.

1. `simp [mu]` to expose both sides.  
2. `exact h_bound`. (the hypothesis already matches the goal after `simp`)

---

## 5  `tail_lt_A`

Strictly less than the head tower.

Step-plan inside the `by` block:

1. `intro A` – keep the `let` binding.  
2. `have h₁ : … ≤ ω^(μ recΔ + 3)` via `termB_le`.  
3. Build `h₂ : μ recΔ + 3 < μ(δ n)+μs+6` using `mu_recΔ_plus_3_lt`.  
4. Lift through powers with `opow_lt_opow_right`.  
5. Chain with `lt_of_le_of_lt`.  
6. `simpa [A]`.

Copy-pattern: lines 800-820 in `Termination_C.lean` (`head_lt_A`).

---

## 6  `mu_merge_lt_rec`

Uses `head_lt_A` + `tail_lt_A`.

1. `set A := ω^(μ(δ n)+μs+6) with hA`.  
2. Invoke the two lemmas → `h_head`, `h_tail`.  
3. Use `omega_pow_add3_lt` to combine:
   `have h_sum := omega_pow_add3_lt … h_head h_tail zero_lt_one`.  
4. Show RHS of rule is `> A` (use definition of μ for `recΔ … δ n`).  
5. `exact lt_trans h_sum h_rhs`.

Pattern: see comments already in file; only mechanical copy, no new maths.

---

## 7  `μκ_decreases`

Only the `R_rec_zero` and duplicated cases need polishing.

For each Step-constructor:
1. Decide whether κ drops (→ `Prod.Lex.left`) or κ equal (→ `μ_to_μκ`).  
2. Call the prepared μ-lemmas (`mu_lt_*`) or `μκ_lt_R_rec_succ`.  
3. `simp [kappa]` whenever κ is syntactically `0`.

The template for all eight cases is already written; only replace “TODO”
with the one-liners above.

---

## 8  `step_strong_normalization_lex`

1. `have wf := InvImage.wf (f := μκ) wf_LexNatOrd`.  
2. `apply Subrelation.wf _ wf`.  
3. `intro x y hxy; exact μκ_decreases hxy`.

Copy-pattern: earlier μ-only proof but swap `mu` → `μκ`.

---

## 9  Remove legacy μ-route

• Delete everything below the dashed block in `Termination_C.lean` that still
  references `rec_succ_bound`, including `mu_decreases` and the old SN theorem.

---

### Finishing checklist

1. After each lemma is filled, run `lake build`.  
2. If Lean flags an `unknown identifier`, go to ordinal-toolkit.md and verify
   the exact spelling; never invent.  
3. Ensure `#print axioms` shows an empty list.  
4. Commit.

Happy mechanising! :rocket:



## LATEST UPDATE - 8/7/2025 8:50 PM - O3


TL;DR – Your remaining blocker is still the missing right-monotonicity of ordinal addition.
add_lt_add_right (and its ≤ twin) must stay on the project’s red list because the property they state is false for ordinals once the right-hand addend can jump over ω.
The fix is not to bend the library: either (A) keep that inequality as an external hypothesis (your “h_bound” pattern), or—much better—(B) finish the migration to the lexicographic (κ, μ) measure sketched in Termination_Plan.md.
Below you’ll find a detailed autopsy of the current file, why the proof still stalls, and a menu of two sound repair strategies (with sub-tasks and risk notes).

1 Where the proof is stuck now
1.1 The new attempt in Termination_C.lean
You replaced the bogus tower-swap lemma with a refined μ (the ω^(μ n + μ s + 6) head absorbs μ s).

The critical inequality now lives in mu_merge_lt_rec.

Inside that lemma you use

lean
Copy
Edit
exact lt_of_lt_of_le h1
  (le_of_lt (lt_trans h2 (lt_add_of_pos_right A zero_lt_one)))
which tacitly relies on x < A ∧ y < A ⇒ x + y + 1 < A.
That step in turn needs right-monotone < for +, i.e. add_lt_add_right.

1.2 Why Lean can’t supply it
Ordinal.add is not strictly (or even weakly) monotone in the right argument:

lua
Copy
Edit
1 + ω  = ω
2 + ω  = ω            -- not strictly larger!
A direct counter-example exists in mathlib and the literature 
Mathematics Stack Exchange
.
Hence add_lt_add_right is provably wrong for ordinals once the right addend may be ≥ ω.
Mathlib therefore marks it @[simp] only for additive monoids that do enjoy commutativity; Ordinal is deliberately excluded 
GitHub
.

1.3 Status of add_lt_add_right in your own rules
The traffic-light table in ordinal-toolkit.md already lists
add_lt_add_right under the red column (non-portable, violates Rule 2) ordinal-toolkit, so the toolchain is consistent: it forbids its use.

2 Two viable ways forward
Strategy	What changes?	Pros	Cons / Risks
A. Externalise the gap	Keep current μ; turn the missing bound into an explicit hypothesis h_merge_rec (same style as your existing h_bound). All downstream lemmas thread it.	Minimal edits; lets you continue developing confluence & Gödel layer while the arithmetic team investigates a tighter bound.	SN remains conditional on an un-proved premise. Publication-grade artefact still missing.
B. Switch to the κ-μ lexicographic measure (the plan already drafted in Termination_Plan.md)	Define κ : Trace → ℕ counting δ-height; order traces by (κ, μ) under Prod.Lex. The problematic rec_succ step then decreases κ strictly and can increase μ safely.	Unconditional SN; avoids right-add monotonicity completely; uses only green-listed lemmas (Prod.Lex.left/right).	Requires touching every decrease lemma once again, but the cookbook in Termination_Plan.md is already scripted line-by-line; risk is bounded.

Recommendation: adopt Plan B—it is the clean, axiom-free path and matches Girard-style ordinal measures used in classical SN proofs 
MathOverflow
.

3 What to do with add_lt_add_right
Keep it red-listed in ordinal-toolkit.md; the reasoning above shows it cannot be used safely.

Point reviewers to the counter-example 1 + ω = ω vs 2 + ω = ω (Lean proves this in one line with simp).

If a future lemma really needs some right-addition monotonicity, restrict it to the finite case (c < ω) and prove a bespoke helper:

lean
Copy
Edit
lemma add_lt_add_right_finite
  (h : a < b) (hc : c < omega0) : a + c < b + c
This is admissible (uses lt_omega0 plus left-monotone add_lt_add_left) and stays in the green zone 
Mathematics Stack Exchange
.

4 Detailed repair checklist (Plan B)
4.1 Create the κ measure
@[simp] def κ : Trace → ℕ mirroring the skeleton in Companion.

Add μκ : Trace → ℕ × Ordinal := fun t => (κ t, μ t).

4.2 Eight new decrease lemmas
Six cases are identical (Prod.Lex.right using existing μ lemmas).

R_rec_succ uses Prod.Lex.left because κ drops from k.succ to k.

No right-addition lemma is needed anywhere.

4.3 Plug into InvImage.wf
lean
Copy
Edit
have wf := InvImage.wf (f := μκ) (Prod.lex_wf Nat.lt_wf Ordinal.lt_wf)
4.4 Drop legacy axioms & stale code
Delete rec_succ_bound, its alias, and every comment that references the “tower swap” trick.

Grep for have this shadow-rewrite pattern (seven spots reported) and rename variables to avoid hidden overrides.

5 Side notes & useful references
Lean Zulip thread “Ordinal addition is not right-strict” confirms the library design choice 
CS Lean
.

Standard ordinal textbooks (e.g. Jech ch. 2) give the same counter-example; see the quick proof on Math.SE 
Mathematics Stack Exchange
.

For the lexicographic technique in SN see the MathOverflow discussion on terminating reduction orders 
MathOverflow
.

If you need Lean snippets: mathlib’s Prod.Lex API is documented in the source 
GitHub
.

6 Take-away
Yes, add_lt_add_right must stay red-listed. The ordinal counter-example is fundamental.

Your current μ-only attempt still smuggles that lemma in via a hidden “sum < tower” step—hence the blockage.

Choose: keep the inequality as an assumption (quick but conditional) or finish the lexicographic refactor (clean, unconditional).

Whichever path you pick, audit the shadowed-identifier pattern so Lean can no longer be “happy while mathematics isn’t”.

Good luck—once this hurdle is cleared, the rest of the SN & confluence pipeline should fall into place quickly.









Sources

Ask ChatGPT
