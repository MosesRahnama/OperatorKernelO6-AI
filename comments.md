This is salvageable. What was wrong with the version you pasted can be grouped into a few concrete categories, then I’ll give you corrected, copy-paste-ready versions of the three core pieces (the inner bound, the void-void corner, and the total mu_lt_eq_diff) that avoid those mistakes.

What was broken / needed fixes
Overcomplicated & fragile inner bound (mu (merge a b)+1 < ω^(C+5))

You rederived bounds manually, introducing ad-hoc commutativity/absorption reasoning for ordinal addition (e.g., trying to swap/add μa and μb) with sorrys and unproven equalities.

Instead, the pattern in the working base file is:

Use termA_le and termB_le to bound the two ω-powers.

Show each of those is strictly below ω^(C+5) via monotonicity (opow_lt_opow_right) by chaining μa ≤ C and μb ≤ C.

Show the finite +2 is also below ω^(C+5) since 2 < ω ≤ ω^(C+5).

Combine with omega_pow_add3_lt to get the strict sum bound.

Your code got stuck proving equalities like ω^(C+4) + (ω^(C+4) + 2) = ω^(C+4)*2 + 2 instead of directly using the inequality chain.

Absorption step in the main lemma (4 + C = C) lacked its hypothesis wiring cleanly

You attempted to absorb 4 into C without structured use of mu_sum_ge_omega_of_not_both_void to get ω ≤ C, then feeding that into nat_left_add_absorb. That hypothesis must be derived via the case split and passed explicitly; otherwise the absorption is unjustified.

Case split was implicit / tangled

The total lemma needs to handle a = void ∧ b = void separately so it does not rely on the ω ≤ C absorption assumption in that corner. Your sketch had that idea, but the working code showed tangled assumptions and unproven sorry placeholders for “substantial terms”.

Use of nonexistent or unavailable lemmas / names

There were references like mul_three and attempts to use commutativity/absorption of ordinals in ways not available without proving or using the proper library lemmas.

You must restrict to the existing lemmas (termA_le, termB_le, omega_pow_add3_lt, opow_lt_opow_right, mu_sum_ge_omega_of_not_both_void, nat_left_add_absorb, etc.)—which the corrected code does.

Chaining inequalities more directly

Instead of trying to prove exact rewrites for sum-to-multiplication or juggling equalities, the corrected approach breaks each step into a have with a clear inequality and uses transitivity/combination at the end.