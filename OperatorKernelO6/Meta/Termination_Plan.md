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