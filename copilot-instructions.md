# Copilot Instructions for OperatorKernelO6

## ALGORITHMIC INTERVENTION: Ordinal Name Resolution

### PHASE 1: Error Analysis (MANDATORY)
When encountering ANY Lean error involving ordinals:
1. **STOP** - Do not suggest any solution yet
2. **SCAN** - Read 100 lines before/after error location using `grep_search` with pattern:
   ```
   omega0|opow|Ordinal\.|Order\.|mul_lt|mul_le|add_le|cast_le
   ```
3. **EXTRACT** - List ALL ordinal operations used in surrounding code

### PHASE 2: Name Verification (STRICT CHECKPOINT)
Before suggesting ANY ordinal lemma/tactic:
1. **CHECK LOCAL CODE FIRST**:
   ```
   grep_search "exact lemma_name" in current file
   grep_search "theorem lemma_name" in OperatorKernelO6/
   ```
2. **CHECK ORDINAL TOOLKIT**:
   - Search `core_docs/ordinal-toolkit.md` for EXACT name
   - If found → use with EXACT qualification (e.g., `Ordinal.mul_lt_mul_of_pos_left`)
   - If NOT found → STOP, use GREEN-CHANNEL

3. **FORBIDDEN PATTERNS** (will cause errors):
   - ❌ `mul_le_mul_left` (generic monoid version)
   - ❌ `Ordinal.opow_lt_opow_right` (removed from mathlib)
   - ❌ Unqualified `opow_add` (must be `Ordinal.opow_add`)
   - ✅ Use `Ordinal.mul_le_mul_left'` (primed version for ordinals)

### PHASE 3: Solution Generation (COPY EXISTING PATTERNS)
1. **MIMIC LOCAL PROOFS** - If similar proof exists in file, copy its structure:
   ```lean
   -- Example from Termination_C.lean line 150:
   have hb : 0 < (omega0 ^ (3 : Ordinal)) :=
     (Ordinal.opow_pos (b := (3 : Ordinal)) (a0 := omega0_pos))
   ```

2. **GREEN-CHANNEL PROTOCOL** for new lemmas:
   ```lean
   /-- GREEN-CHANNEL: ordinal helper proven elsewhere -/
   lemma your_new_lemma : ... := by
     sorry  -- TODO-proof: implement using ordinal-toolkit patterns
   ```

### CRITICAL: Mathlib Version Lock
- **NEVER** run `lake update mathlib`
- **NEVER** modify `lake-manifest.json`
- Current mathlib is FROZEN at working commit

### Verification Gates:
- ✅ Every ordinal operation matches pattern in `ordinal-toolkit.md`
- ✅ Every lemma name verified in local code OR toolkit
- ✅ `lake build` passes without unknown identifier errors
- ✅ No generic monoid lemmas used for ordinal arithmetic

## STRICT DISCIPLINE RULES:

### NO PIVOTS WITHOUT JUSTIFICATION
- ❌ "Actually, let me try something simpler"
- ❌ "There's a better way"
- ✅ Stick to the approach until proven impossible
- ✅ Any major change requires FULL mathematical justification

### NO SORRY CHAINS
- ❌ Creating empty lemmas with `sorry` to skip problems
- ❌ Assuming future proofs will fix current issues
- ✅ Solve the actual problem or use GREEN-CHANNEL
- ✅ Every `sorry` must have concrete TODO-proof plan

### MATHEMATICAL CONSISTENCY
- **Every lemma contributes to the larger proof chain**
- **Check implications: "If I prove X this way, does it support theorem Y?"**
- **Verify type signatures match downstream usage**
- **Test edge cases (n=0, void traces, reflexive cases)**

## ENFORCEMENT: 
**Before EVERY ordinal suggestion, output:**
```
PHASE 1 SCAN: Found N ordinal patterns in context
PHASE 2 CHECK: lemma_name found in [location] OR "0 results - using GREEN-CHANNEL"
PHASE 3 COPY: Mimicking proof structure from line X
MATH CHECK: This proof supports [downstream theorem] by establishing [property]
```
