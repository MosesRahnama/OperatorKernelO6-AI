# AGENT.md (stub) — read `core_docs/ko6_guide.md` instead

**This file is deprecated.** For all agent rules, lemma-lookup protocol, and outputs:
- Open `core_docs/ko6_guide.md`, §4 “Interaction Protocol & Lemma-lookup”
- Import/ordinal rules live in §8 “Canonical Imports & Ordinal Basics”

Prime directive and search-first protocol are unchanged:
- Don’t touch the kernel; don’t hallucinate imports/lemmas; no axioms. 
- Always **search first** across repo + docs; if no hit, use **GREEN-CHANNEL** (see §4).
