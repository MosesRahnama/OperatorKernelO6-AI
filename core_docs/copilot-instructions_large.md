```
# DEPRECATED — use `core_docs/ko6_guide.md` + `core_docs/copilot-instructions.md`

This file is archived. The **Single Source of Truth** is:
- `core_docs/ko6_guide.md` (imports, ordinal API, green-channel rules)
- `core_docs/copilot-instructions.md` (enforcement & search-first protocol)

Agents must search SSOT first; echo hit counts; if 0 hits → GREEN-CHANNEL stub.
3) 30-second sanity check
Open Copilot Chat and type:
“Search for mu_lt_rec_zero per SSOT protocol and show hit counts.”
It should print Found N matches (SSOT/code).

Try a fake name: mu_totally_fake.
It should print 0 results — using GREEN-CHANNEL.