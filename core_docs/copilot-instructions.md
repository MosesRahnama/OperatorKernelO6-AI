# Copilot Instructions — OperatorKernelO6 (SSOT-aware)

## Search-First Development (MANDATORY)

**Path priority (must search in this order):**
1) `core_docs/ko6_guide.md`  ← **SSOT**
2) `OperatorKernelO6/**.lean`
3) Stubs: `core_docs/agent.md`, `core_docs/ordinal-toolkit.md` (pointers only)

**Protocol (before suggesting ANY identifier/tactic/lemma):**
- Run a search (ripgrep / #search / #leansearch) over (1)-(2).
- Then **echo** one of:
  - `Found N matches (SSOT/code).`
  - `0 results — using GREEN-CHANNEL.`
- If ≥1 hit → you may use the identifier exactly as found.
- If 0 hits → propose a GREEN-CHANNEL stub:

```lean
/-- GREEN-CHANNEL: new helper for [one-line rationale] --/
lemma <choose_a_name> : _ := by
  "FULL PROOF RIGHT TEHRE"  -- NOT A SINGLE LINE ALLOWED UNTIL FULL PROOF FOR THE HELPER
Enforcement Gates (don’t skip)
Never invent lemma names. Verify first; copy exact spelling and qualification.

Use only the ordinal API and names listed in SSOT §8 (imports, prefixes, do-not-use list).

No axioms, no admit, no partial stubs left behind.

Save ⇒ lake build ⇒ fix only the lines that error until Problems panel is clean.

Ordinal API (summary; full list in SSOT §8)
WF: WellFounded.prod_lex, wellFounded_lt, Ordinal.lt_wf

ω-powers: opow, opow_add, Ordinal.opow_le_opow_right

Products: Ordinal.mul_lt_mul_of_pos_left, Ordinal.mul_le_mul_iff_left, mul_le_mul_left'

Successor bridge: Order.lt_add_one_iff, Order.add_one_le_of_lt

Forbidden: generic mul_le_mul_left (non-ordinal), unqualified names (opow_add), deprecated lemmas.

Build-and-Fix Loop
Save file → lake build runs.

If any error: show “PHASE 1/2/3” header:

PHASE 1 SCAN: list ordinal ops around the error.

PHASE 2 CHECK: show where each lemma name was found (path+line) or say “0 results — GREEN-CHANNEL”.

PHASE 3 COPY: name the template proof you’re copying (file+line).

Apply smallest change; rebuild; repeat.

Why SSOT?
All canonical rules, imports, and ordinal usage live in core_docs/ko6_guide.md. Treat it as law. (agent.md and ordinal-toolkit.md are stubs that point back to SSOT.)

