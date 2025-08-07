# Copilot Instructions for OperatorKernelO6

## GOLDEN RULE: Search-First Development
**Every theorem, lemma, or constant name MUST exist in one of these sources before use:**
1. Local repository documentation (`core_docs/`, `Docs/`)
2. Compiled Lean environment (via `#leansearch` or `#search`)
3. Current project files (`OperatorKernelO6/`, `Main.lean`)

## Workflow Protocol

### Before suggesting ANY identifier:
1. **Run `#search "description"` or `#leansearch "identifier_name"`**
2. **Echo the search hit count in chat** (e.g., "Found 3 matches" or "0 results - using GREEN-CHANNEL")
3. **If results found** → proceed with suggestion
4. **If NO results found** → use GREEN-CHANNEL protocol

### GREEN-CHANNEL Protocol (for new helpers):
```lean
/-- GREEN-CHANNEL: new helper for [brief rationale] --/
lemma your_new_lemma : ... := by
  sorry  -- TODO-proof: implement this [username]
```

### Build-and-Fix Loop:
1. Every completion triggers save
2. Save triggers `lake build`
3. Build errors trigger Copilot `/fix` action
4. Fix only the broken lines, preserve working code

## Key Documentation Sources:
- `core_docs/ko6_guide.md` - Main project guide
- `core_docs/Termination_Companion.md` - Termination analysis
- `core_docs/ordinal-toolkit.md` - Ordinal operations
- `OperatorKernelO6/Kernel.lean` - Core definitions
- `OperatorKernelO6/Meta/` - Meta-theory implementations

## Search Commands Available:
- `#search "natural language description"`
- `#leansearch "exact_identifier"`
- `#moogle "fuzzy search"`
- `#loogle "type signature"`

## Error Recovery:
- Compile errors → immediate `/fix` suggestion
- Unknown constants → check docs first, then GREEN-CHANNEL
- Type mismatches → search for existing conversion lemmas

## Quality Gates:
- ✅ All identifiers found in search OR marked GREEN-CHANNEL
- ✅ Code compiles with `lake build`
- ✅ No undefined constants in Problems view
- ✅ All `sorry` marked with TODO-proof rationale

Remember: **SEARCH FIRST, CREATE SECOND**. This prevents hallucinated identifiers and maintains mathematical rigor.
