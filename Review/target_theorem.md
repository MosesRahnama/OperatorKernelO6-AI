# Target Theorem (initial skeleton)

_This file will hold the evolving proof we are working on.  For now it is just a placeholder so that future edits can patch it with minimal diffs._

---

# Ordinal Termination Proof: `tail_lt_A`

## Theorem statement

```lean
lemma tail_lt_A {b s n : Trace} :
    let A : Ordinal := omega0 ^ (mu (delta n) + mu s + 6)
    omega0 ^ (2 : Ordinal) * (mu (recΔ b s n) + 1) < A
```

## Proof outline - The Simple Version

We'll use this core approach:

1. **Step 1**: Show that `ω²·(μ(recΔ b s n)+1) ≤ ω^(μ(recΔ b s n)+3)`
   - This uses the general bound `termB_le` which gives a tighter exponent representation

2. **Step 2**: Show that `μ(recΔ b s n) + 3 < μ(δ n) + μ s + 6`
   - First, we prove `μ(recΔ b s n) < ω^α` where `α = μ n + μ s + 6`
   - Using `opow_mul_lt_of_exp_lt` to handle the tower structure
   - Then show `μ n < μ(δ n)` via `mu_lt_delta`
   - Chain these inequalities together with appropriate transitivity steps

3. **Step 3**: Apply strict monotonicity of ω-powers:
   - `μ(recΔ b s n) + 3 < μ(δ n) + μ s + 6` implies
   - `ω^(μ(recΔ b s n) + 3) < ω^(μ(δ n) + μ s + 6)`

4. **Final Step**: Chain the inequalities from Steps 1 and 3:
   - `ω²·(μ(recΔ b s n)+1) ≤ ω^(μ(recΔ b s n)+3) < A`

## Key Insights

1. **Ordinal arithmetic**: The proof relies on properties of ordinal exponentiation where `ω^a · ω^b = ω^(a+b)`

2. **Tower absorption**: The much larger tower `A = ω^(μ(δ n) + μ s + 6)` dominates the recursive term

3. **Recursive structure**: The `recΔ` constructor creates a term whose `μ` measure is strictly less than the `μ` of `δ n`

4. **Decomposition strategy**: We separate the inequality into manageable steps, first obtaining a cleaner representation of the left side, then proving the key exponent inequality
