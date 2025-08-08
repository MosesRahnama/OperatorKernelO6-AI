# ordinal-toolkit.md (stub) — read `core_docs/ko6_guide.md` §8

**This file is deprecated.** The authoritative ordinal toolkit is now in
`core_docs/ko6_guide.md` §8 “Canonical Imports & Ordinal Basics”.

Keep these rules **exactly** as written there:
- Use the import whitelist (WF, Prod.Lex, Ordinal.Basic/Arithmetic/Exponential, etc.).
- Qualification rules: `Ordinal.opow_le_opow_right`, local `opow_lt_opow_right`, 
  `Ordinal.mul_lt_mul_of_pos_left`, `Ordinal.mul_le_mul_iff_left`, and `Order.lt_add_one_iff`.
- Never use generic `mul_le_mul_left` for ordinals.

See §8 for the full table and examples.
