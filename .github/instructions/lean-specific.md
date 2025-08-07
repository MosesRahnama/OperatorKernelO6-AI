# Lean-Specific Instructions

**Applies to:** `**/*.lean`

## Lean Development Protocol

### Before writing ANY Lean code:
1. **Import LeanSearchClient**: `import LeanSearchClient`
2. **Search existing definitions**: Use `#search`, `#leansearch`, or `#loogle`
3. **Verify in local docs**: Check `core_docs/` for project-specific definitions

### Search Workflow:
```lean
-- ALWAYS do this first:
#search "description of what you need"
-- OR
#leansearch "exact_name_you_think_exists"
-- OR  
#loogle "Type → Type → Prop"  -- for type signatures
```

### Project-Specific Imports:
```lean
import OperatorKernelO6.Kernel              -- Core definitions
import OperatorKernelO6.Meta.Termination    -- Termination analysis
import OperatorKernelO6.Meta.Meta           -- Meta-theory
-- Only import others if actually needed
```

### GREEN-CHANNEL for New Definitions:
```lean
/-- GREEN-CHANNEL: [one-line explanation why this is needed] --/
def new_definition : Type := sorry

/-- GREEN-CHANNEL: helper for ordinal arithmetic bounds --/
lemma ord_bound_helper (α β : Ordinal) : α < β → ... := by
  sorry  -- TODO-proof: implement using existing ordinal lemmas
```

### Error Recovery Patterns:
- `unknown identifier` → `#search` the name first
- `type mismatch` → look for conversion lemmas in mathlib
- `failed to synthesize` → check if typeclass instances exist

### Build Quality Checks:
- No `sorry` without GREEN-CHANNEL comment
- All imports actually used
- No duplicate definitions (search first!)
- Compile clean with `lake build`
