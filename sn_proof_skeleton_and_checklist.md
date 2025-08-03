**Assistant's Note:** Is this the whole intended checklist? My view: The structure is sound and covers the critical inequalities and dependencies; key cautions are ensuring strictness where required for limit absorption, verifying `omega0 ≤ C` before using absorption, and handling corner cases (e.g., both-void) explicitly. Below is the checklist as provided.

# Strong Normalization Proof Skeleton and Checklist

## A. mu\_lt\_eq\_diff and merge\_inner\_bound\_simple (inner core) - Summary

(Condensed from earlier plan; no code here, only what must be true and checked.)

### 1. Inner bound (`merge_inner_bound_simple`)

Goal: With C := mu a + mu b, show:

```text
mu (merge a b) + 1 < omega0^(C + 5)
```

Checklist:

-

### 2. Total lemma `mu_lt_eq_diff` (with case split)

Goal: `mu (integrate (merge a b)) < mu (eqW a b)`. Checklist:

-

## B. Required lemmas / properties (verify presence in existing code)

-

## C. Extension to full SN proof (high-level skeleton beyond current lemma)

Checklist:

-

## D. Early warning signs / dead ends (what to watch for)

-

## E. Next Milestones

1. Finalize and verify `merge_inner_bound_simple` and `mu_lt_eq_diff` with all dependencies green.
2. Eliminate any remaining `sorry` in measure-decrease chain (`mu_decreases`, `mu_lt_rec_succ`, etc.).
3. Complete the well-foundedness argument to seal strong normalization.
4. Perform a consistency audit: ensure no circular dependencies and all used lemmas are from whitelisted sources.
5. Prepare a concise math write-up for the paper describing the structure of the SN proof, referencing this checklist.

*End of skeleton.*

