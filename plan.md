1. What’s wrong with the current mu\_lt\_eq\_diff variant

### a. Inner bound is too weak or improperly handled

You lean on `payload_bound_merge_mu a` to get

```
mu (merge a b) + 1 ≤ omega0^(mu a + 5)
```

then try to promote that to

```
< omega0^(C + 5) with C := mu a + mu b.
```

That fails to give a strict inequality in the case mu b = 0 (so C = mu a), because

```
omega0^(mu a + 5) = omega0^(C + 5).
```

You need the symmetric combination of head and tail — i.e., both omega0^3 \* (mu a + 1) and omega0^2 \* (mu b + 1) — and then use the principal ordinal bound (the `omega_pow_add3_lt` pattern) to get

```
mu (merge a b) + 1 < omega0^(C + 5)
```

uniformly. In other words, replace the one-sided payload bound with the `merge_inner_bound_simple` style argument that uses `termA_le`, `termB_le`, and `omega_pow_add3_lt`. (If there remain problematic edge cases when one of mu a, mu b is zero, those must be handled explicitly — you already split off the both-void case; you may need an analogous consideration if exactly one is void depending on what the existing bounds give.)

### b. Exponent comparison is incorrect / illegally manipulates ordinals

The critical step to show

```
(4 : Ordinal) + (C + 5) < C + 9
```

is handled by doing something like reducing to `C + 4 < C + 9` and then `simpa [add_comm, add_left_comm, add_assoc]` — this is not sound in general because ordinal addition is not commutative, and you’ve not invoked the correct absorption lemma. The intended correct derivation is: from `omega0 ≤ C` use `nat_left_add_absorb` to get `4 + C = C`, so

```
4 + (C + 5) = (4 + C) + 5 = C + 5 < C + 9
```

via `5 < 9`. You must explicitly use that absorption with the precondition `omega0 ≤ C`; the current ad-hoc manipulation is fragile and potentially false.

### c. Missing / informal justification of the precondition `omega0 ≤ C`

The absorption step requires `omega0 ≤ C` (i.e., `omega0 ≤ mu a + mu b`), which does not hold in the corner `a = void ∧ b = void` — you need the case split (you have a separate void-void lemma, good). For the general branch you must derive `omega0 ≤ C` via the proven helper lemma `mu_sum_ge_omega_of_not_both_void`. Any ad hoc “assumption” or `sorry` here kills soundness; that derivation must be solid and use only the whitelisted patterns (case analysis, `nonvoid_mu_ge_omega`, etc.).

### d. Potential mismatch between `mu t + 1` and `Order.succ (mu t)`

Your system has a recurring tension between using `mu t + 1` versus `Order.succ (mu t)` in bounds. Some helper lemmas and monotonicity reasoning in the base file expect the successor form; mixing them without explicit bridging can cause type/goal mismatches. You need either an adapter lemma (e.g., `mu t + 1 = Order.succ (mu t)`) or consistently use one shape so the lifted comparisons line up without hidden coercion failures.

### e. Style / duplication — not fatal but improvable

You reinvent the final unfolding in place instead of reusing `core_mu_lt_eq_diff_from_prod` or the `finish_mu_lt_eq_diff` wrapper. Refactoring to leverage the already green finalizer reduces surface area for mistakes and keeps logic modular.

2. What must be done to salvage it

- Replace the inner bound with the full `merge_inner_bound_simple` style argument: use `termA_le` and `termB_le` to get each payload piece strictly under `omega0^(C + 5)`, plus the finite part 2, then apply `omega_pow_add3_lt` to aggregate. Ensure strictness uniformly or split off necessary subcases (void / one side zero).
- Formalize the case split in `mu_lt_eq_diff`:
  - Explicitly handle `a = void ∧ b = void` via the both-void lemma.
  - In the general case, invoke `mu_sum_ge_omega_of_not_both_void` to get `omega0 ≤ C`.
- Fix exponent absorption correctly: from `omega0 ≤ C`, apply `nat_left_add_absorb` to absorb the 4, derive `4 + (C + 5) = C + 5 < C + 9` using `5 < 9`. Drop any use of `add_comm` or unsafe commutativity rewriting; stick to the proven pattern.
- Chain inequalities and finish via existing finalizer: multiply the inner bound by `omega0^4`, collapse via `omega0^4 * omega0^(C + 5) = omega0^(4 + (C + 5))`, apply absorption to reduce to `omega0^(C + 5) < omega0^(C + 9)`, add 1, and then unfold `mu` on both sides. Prefer using `core_mu_lt_eq_diff_from_prod` or `finish_mu_lt_eq_diff` to consolidate the last step.
- Audit helper lemmas (`mu_sum_ge_omega_of_not_both_void`, `nonvoid_mu_ge_omega`) to ensure they use only safe patterns (no hidden commutativity assumptions, correct case splits).
- Eliminate all remaining `sorry`s in this region; they are placeholders for missing logical content and must be replaced with rigorous versions above.

3. Is the project astray? No. The architecture is coherent and sound: the measure `mu`, the void versus general case split, the inner merge bound, the absorption principle, and the final chaining to strong normalization fit the standard blueprint. Current blockages are implementation-level: delicate ordinal arithmetic (absorption and strictness), mixing of successor vs `+1`, and overreaching rewrites. Correcting those with the existing patterns will yield a clean build. It’s in the polishing phase, not astray.

4. Rough timeline to finish and publication feasibility *Technical completion (strong normalization proof)*

- Fix core lemmas (`merge_inner_bound_simple`, corrected `mu_lt_eq_diff`, void case): \~3–5 hours if using existing proven patterns.
- Audit and finalize helper lemmas, remove leftover `sorry`s: \~1–2 hours.
- Full build / edge case debugging / regression: \~1–3 hours.
- Proof housekeeping (wrappers, naming, refactors): \~1 hour. Subtotal technical: \~6–11 hours.

*Writeup / submission*:

- Exposition draft: \~1–2 days if draft exists, 3–4 days from scratch.
- Review / formatting / arXiv prep: 1 day buffer.

*Feasibility for before 2 p.m. Thursday*: If you can secure a green build in Day 1 and work in parallel on write-up, it’s tight but plausible. Key risks are stubborn corner-case inequalities and underestimated writing time.

*Summary recommendation* Immediate: fix inner bound and exponent absorption exactly per canvas plan, solidify precondition `omega0 ≤ C` via existing helper, isolate the void case. Next: clean up, compile, and remove all `sorry`s. Parallel: draft the paper, including the pattern-analysis methodology.

Would you like a concise stand‑alone checklist (no code) of the exact inequalities/lemmas to tick off in order next?


# Strong Normalization Proof Skeleton and Checklist

**Assistant's Note:** Is this the whole intended checklist? My view: The structure is sound and covers the critical inequalities and dependencies; key cautions are ensuring strictness where required for limit absorption, verifying `omega0 ≤ C` before using absorption, and handling corner cases (e.g., both-void) explicitly. Below is the checklist as provided.


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

