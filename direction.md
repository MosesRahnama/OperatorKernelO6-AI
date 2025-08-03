Mathematical outline (“explain to a newcomer”)
Objective
Show that for every constructor except .void, the μ-measure is
at least ω:
ω ≤ μ t.

Key facts

Fact	Reason
ω ≤ ωᵏ for any k ≥ 1	ω-powers are strictly increasing.
If 1 ≤ x, then c ≤ c·x	Left-multiplication by a positive ordinal is monotone.
y ≤ y + 1	Adding a non-negative ordinal preserves order.

Constructor analysis

δ s μ = ω⁵·(μ s+1)+1
ω ≤ ω⁵ ≤ ω⁵·(μ s+1) ≤ ω⁵·(μ s+1)+1 = μ.

∫ s same with exponent 4.

merge a b μ = ω³·(μ a+1)+ω²·(μ b+1)+1
First show ω ≤ ω²·(μ b+1)+1, then add the non-negative left summand
ω³·(μ a+1).

recΔ b s n, eqW a b similar, with variable ω-exponent
towers; inequality holds because the leading ω-tower already exceeds
ω.

Associativity bookkeeping
Lean’s simp [mu] rewrites only if the
parenthesisation matches. The extra annotation
[add_comm, add_left_comm, add_assoc] normalises + so that
(ωᵏ·(μ+1))+1 matches the literal definition of μ and the final
simpa closes each branch.

Code ↔ Math mapping
Code block	Math step
hω_pow	ω ≤ ωᵏ
h_one_le	1 ≤ μ + 1
mul_le_mul_left' + rw [mul_one]	lift through multiplication
le_add_of_nonneg_right	append +1
nested le_add_of_nonneg_left in merge	add the extra positive summand
final simpa [mu, …]	equate RHS to the μ-definition

With the explicit rw [mul_one] Lean now sees the exact left-hand term
it needs, all metas disappear, and nonvoid_mu_ge_omega compiles.