# `tail_lt_A` – Current failure & proposed rewrite 🛠️

This note accompanies `diag_1.txt`, which contains the full Lean
diagnostics.  It records:

* why the present 180-line proof fails,
* the minimal patch strategy,
* concrete TODOs.

---

## 1  High-level summary

`tail_lt_A` fails for three independent reasons.

| Label | Root cause | Fix in new proof |
|-------|------------|------------------|
| **A** | Wrong call to `add_lt_add_left` loses the padding term. | Avoid the padding trick; compare exponents directly. |
| **B** | Two non-existent lemmas are referenced:<br> `Ordinal.le_of_lt_add_of_pos`,<br> `Ordinal.IsNormal.strictMono_iff`. | Do not rely on them; use `opow_lt_opow_right` instead. |
| **C** | Several goals stay open because of fragile `simp/rw` chains. | Replace the full script with a 40-line direct argument (see § 3). |

---

## 2  Key excerpt from Lean

```text
Termination.lean:867:10  type mismatch
… expected `μ n + (μ s + 6) < μ n.delta + (μ s + 6)`
but got       `μ n < μ n.delta`
```

Additional missing constants and unsolved goals are listed in
`diag_1.txt`.

---

## 3  Recommended replacement strategy  🚀

1. **Shrink the goal**  
   Reduce to  
   `μ(recΔ …) + 3 < μ(δ n) + μ s + 6`.

2. **Use ω-power monotonicity**  
   ```
   from  μ(rec)+1 < A
   ⇒     ω^(μ(rec)) < A
   ⇒     μ(rec)     < μ(δ n)+μ s+6
   ⇒     μ(rec)+3  < μ(δ n)+μ s+6
   ```

3. **Combine with `termB_le`**  
   ```
   ω²·(μ(rec)+1) ≤ ω^(μ(rec)+3)
   ω^(μ(rec)+3) < ω^(μ(δ n)+μ s+6)
   --------------------------------
   ω²·(μ(rec)+1) < A
   ```

Total length ≈ 40 lines, relying only on
`termB_le`, `opow_lt_opow_right`, `Principal …`.

---

## 4  Action items

1. Delete the current proof block (lines 830–910 in `Termination.lean`).
2. Insert the shorter argument sketched above.
3. Re-check `mu_merge_lt_rec`, which will continue to compile.

---

*Last updated : 2025-02-21*  
(Lean 4.22 + Mathlib4 nightly)
