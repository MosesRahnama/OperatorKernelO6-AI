1. Inner bound (mu (merge a b) + 1 < ω^(C+5))


What's wrong:

- You used hpayload := payload_bound_merge_mu a to get a bound on mu (merge a b) + 1 ≤ ω^(mu a + 5).
  Issue: merge depends on both a and b. Bounding it solely via mu a ignores the ω²·(mu b + 1) component; the true route is to split into head and tail using termA_le and termB_le and then combine them with something like omega_pow_add3_lt. The current sketch collapses that to a one-sided bound that doesn’t reflect the structure and is too weak/unsound for the general case.
- You never argued that mu a + 5 ≤ C + 5 nor that mu b + 4 ≤ C + 5 in a way that would allow combining into ω^(C+5). In the version above you essentially assume 4 + (C + 5) < C + 9 by manipulating ordinal addition with commutativity/associativity—but ordinal addition is not commutative, so those rewrites are unjustified unless you carefully stay within valid transformations. That taints the exponent comparison downstream.

Fix path:

- Follow the proven pattern:
	1. Use termA_le (x := mu a) to get ω³·(mu a + 1) ≤ ω^(mu a + 4), and termB_le (x := mu b) to get ω²·(mu b + 1) ≤ ω^(mu b + 3).
	2. Show mu a + 4 < C + 5 and mu b + 3 < C + 5 (since mu a, mu b ≤ C := mu a + mu b).
	3. Use opow_lt_opow_right to lift those into strict inequalities of the form ω^(mu a + 4) < ω^(C + 5) and ω^(mu b + 3) < ω^(C + 5).
	4. Note 2 < ω ≤ ω^(C + 5) since C + 5 ≥ 5.
	5. Combine the three smaller ordinals under the limit ω^(C+5) using omega_pow_add3_lt to conclude
	   ω^(mu a + 4) + ω^(mu b + 3) + 2 < ω^(C + 5).
	6. Back out mu (merge a b) + 1 = ω³·(mu a + 1) + ω²·(mu b + 1) + 2 ≤ ω^(mu a + 4) + ω^(mu b + 3) + 2, so the desired strict inequality follows.
That is essentially the clean “merge_inner_bound_simple” you had in the earlier plan; you need to reify it instead of the shortcut using payload_bound_merge_mu a.
---

2. Exponent manipulation and absorption in the main lemma


What's wrong:

- You assert (4 : Ordinal) + (C + 5) < C + 9 by using a numerical fact 4 < 9 and then massaging it with commutativity/associativity (simpa [add_comm, add_left_comm, add_assoc]). This is invalid:
	- Ordinal addition is not commutative, so moving the 4 around without the proper absorption hypothesis is unsound.
	- More importantly, to reduce 4 + (C + 5) to something like C + 5 you need 4 + C = C, which requires the absorption lemma nat_left_add_absorb and the hypothesis ω ≤ C. None of that appears in this version, so the chain ω^(4 + (C+5)) < ω^(C+9) is ungrounded.
- The proof conflates the general case and the corner case (C = 0). For C = 0, the desired absorption 4 + C = C fails (since 4 + 0 = 4 ≠ 0), so the exponent comparison would break: you’d be trying to show ω^(4 + 5) < ω^(0 + 9), i.e., ω⁹ < ω⁹, which is false. Hence the necessity of splitting off the a = void ∧ b = void case separately (as in the earlier total version).

Fix path:

- Case split: handle a = void ∧ b = void separately with concrete numerics (ω³ + ω² + 2 < ω⁵, etc.), as your earlier plan does.
- General case:
	- First obtain C := mu a + mu b and prove ω ≤ C using mu_sum_ge_omega_of_not_both_void.
	- Use nat_left_add_absorb with that to get (4 : Ordinal) + C = C, hence 4 + (C + 5) = C + 5.
	- Now it’s legitimate to compare ω^(4 + (C + 5)) = ω^(C + 5) and use opow_lt_opow_right to get ω^(C + 5) < ω^(C + 9) because C + 5 < C + 9.
---

3. Chaining to the final inequality


What's wrong:

- Because the inner and exponent bounds are shaky, the chain
  ω⁴ * (mu (merge a b) + 1) < ω^(4 + (C + 5)) < ω^(C + 9)
  is not solid. The first inequality depends on the correct inner bound; the second depends on the improper absorption/manipulation. So the key “bridge” lemma is undermined.

Fix path:

- Once the two previous sections are repaired (clean inner bound and valid exponent collapse using absorption under ω ≤ C), the chaining becomes straightforward: multiply the strict inner bound by ω⁴ with Ordinal.mul_lt_mul_of_pos_left, collapse powers with the correct opow_add and use the strict exponent inequality to reach ω^(C+9). Then add +1 using lt_add_one_of_le and finish with simp [mu, hB, hC].
---

Summary: Why it’s salvageable and what to do next

Salvageability:
All the core ideas are correct:
- Decompose mu (merge a b) into head/tail and combine under a higher tower.
- Split the corner case.
- Use absorption to collapse exponents in the general case.
  What’s missing is the precise implementation of those steps with the right existing lemmas and the necessary preconditions made explicit instead of being hand-waved.
Immediate corrections to make it rigorous:
1. Replace the sketchy inner-bound with the proven merge_inner_bound_simple pattern (or implement it directly via termA_le, termB_le, omega_pow_add3_lt, etc.).
2. Split off the (void,void) case entirely instead of relying on the general absorption-heavy route when C=0.
3. In the general branch, explicitly invoke mu_sum_ge_omega_of_not_both_void to get ω ≤ C and then apply nat_left_add_absorb to absorb the 4 when collapsing exponents. Remove any illegal use of add_comm on ordinals unless you’re only using associativity in ways you can justify.
4. Chain the inequalities cleanly: inner bound → multiply by ω⁴ → collapse exponent via opow_add and absorption → compare to ω^(C+9) → add one.
5. Ensure all uses of monotonicity (opow_lt_opow_right, Ordinal.mul_lt_mul_of_pos_left) satisfy their preconditions (strictness, positivity).
---

Hints / early warning signs (dead-end detectors)

- If you try to “massage” 4 + (C + 5) into C + 5 without proving ω ≤ C, that’s a red flag: absorption is being used illicitly.
- Any time you use commutativity on ordinal addition to flip summands without a lemma, stop—ordinal addition isn’t commutative.
- If the inner bound proof only references mu a or only mu b in isolation for merge a b, it’s incomplete.
- Watch the corner case C = 0: any proof that relies on ω ≤ C must not be applied there; that’s why the separate both_void lemma is essential.
---

Verdict

Yes, the current approach can be salvaged, but it must be refactored to:
- Explicitly separate the void-void corner case.
- Use the correct inner bound (using both a and b).
- Introduce and prove the absorption step with ω ≤ C before collapsing exponents.
- Remove any illegal ordinal arithmetic shortcuts (e.g., unproved uses of commutativity or implicit absorption).
