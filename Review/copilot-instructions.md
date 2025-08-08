# Copilot Instructions for OperatorKernelO6

## CRITICAL CONTEXT: Why Termination_C.lean Exists
**The original Termination.lean has a MATHEMATICALLY FALSE lemma `rec_succ_bound`.**
- It claims: `ω^(μ n + μ s + 6) < ω^5·(μ n + 1)` 
- But this is impossible since `ω^5·(μ n + 1) = ω^(μ n + 6) ≤ ω^(μ n + μ s + 6)`
- The proof uses identifier shadowing to trick Lean into accepting it

**Termination_C.lean implements the FIX from Termination_Plan.md:**
- Introduces lexicographic measure (κ, μ) where κ counts recΔ nesting depth
- Seven cases: κ unchanged, μ strictly decreases → lexicographic decrease
- rec_succ case: κ strictly decreases → lexicographic decrease (avoiding the false inequality)
- This gives unconditional strong normalization WITHOUT the false lemma

## CRITICAL: LEMMA VERIFICATION PROTOCOL (MANDATORY FOR ALL AI MODELS)

### THE RED ALERT RUDE! RED ALERT! CHECK BEFORE USE
**NEVER write ANY lemma name without FIRST verifying it exists:**
1. Check `core_docs/ordinal-toolkit.md` for ordinal lemmas
2. Search existing code in `OperatorKernelO6/Meta/` for usage patterns
3. If NOT found in either → IT DOESN'T EXIST, DO NOT USE IT

**This applies to EVERY lemma, EVERY tactic, EVERY theorem name. No exceptions.**

### ENFORCEMENT PROTOCOL
Before writing ANY Lean code, you MUST:
```
STEP 1: Identify needed lemmas
STEP 2: Search ordinal-toolkit.md for EXACT names
STEP 3: Grep existing code for usage patterns
STEP 4: Copy EXACT syntax and tactics
STEP 5: If not found → STOP, do not guess
```

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
   - If NOT found → STOP, DO NOT USE

3. **VERIFIED PATTERNS** (use these exactly):
   ```lean
   -- CORRECT (verified to exist):
   Ordinal.opow_pos
   Ordinal.opow_add  
   Ordinal.opow_succ
   Ordinal.opow_le_opow_right
   Ordinal.mul_le_mul_left'  -- NOTE THE PRIME!
   Ordinal.le_mul_right
   Ordinal.lt_wf
   Ordinal.omega0_pos
   WellFounded.prod_lex  -- NOT Prod.lex_wf
   wellFounded_lt        -- for Nat well-foundedness
   ```

4. **FORBIDDEN PATTERNS** (will cause errors):
   - ❌ `mul_le_mul_left` (generic monoid version - missing prime)
   - ❌ `Ordinal.opow_lt_opow_right` (removed from mathlib)
   - ❌ Unqualified `opow_add` (must be `Ordinal.opow_add`)
   - ❌ `Prod.lex_wf` (doesn't exist - use `WellFounded.prod_lex`)
   - ❌ `Nat.lt_wfRel` (use `wellFounded_lt` instead)

### PHASE 3: Solution Generation (COPY EXISTING PATTERNS)
1. **MIMIC LOCAL PROOFS** - If similar proof exists in file, copy its structure:
   ```lean
   -- Example from Termination_C.lean line 150:
   have hb : 0 < (omega0 ^ (3 : Ordinal)) :=
     (Ordinal.opow_pos (b := (3 : Ordinal)) (a0 := omega0_pos))
   ```

2. **COPY TACTIC PATTERNS** - Use exact tactics from working code:
   ```lean
   -- For lexicographic ordering (from working code):
   apply Prod.Lex.left   -- when first component decreases
   apply Prod.Lex.right  -- when first equal, second decreases
   ```

3. **NO NEW LEMMAS UNLESS WE CAN DEFINE AND PROVE THEM** - We have 1300+ lines of working code. Everything needed is there.

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
- ❌ ANY use of `sorry` in final code
- ✅ Complete every proof using existing patterns

### MATHEMATICAL CONSISTENCY
- **Every lemma contributes to the larger proof chain**
- **Check implications: "If I prove X this way, does it support theorem Y?"**
- **Verify type signatures match downstream usage**
- **Test edge cases (n=0, void traces, reflexive cases)**

## COPY-PASTE PROTOCOL
Since we have extensive working code, most tasks are copy-paste:
1. **Find similar proof** in existing files
2. **Copy exact structure** including tactics
3. **Adapt variable names** only
4. **Keep same proof flow**

Example workflow:
```
User: "Prove lemma X about ordinals"
AI: 
1. Search ordinal-toolkit.md for relevant lemmas
2. Grep OperatorKernelO6/ for similar proofs
3. Copy proof structure exactly
4. Verify with lake build
```

## ENFORCEMENT: 
**Before EVERY code edit, output:**
```
PHASE 1 SCAN: Found N ordinal patterns in context
PHASE 2 CHECK: lemma_name found in [location] OR "NOT FOUND - STOPPING"
PHASE 3 COPY: Mimicking proof structure from line X
MATH CHECK: This proof supports [downstream theorem] by establishing [property]
```

## COMMON MISTAKES THAT WASTE TIME:
1. **Guessing lemma names** → Always verify first
2. **Creating new proof strategies** → Copy existing ones
3. **Using wrong lemma versions** → Check for primes and qualifications
4. **Leaving sorries** → Complete every proof
5. **Taking U-turns mid-proof** → Stick to the plan

## SUCCESS CRITERIA:
- Zero `sorry` in code
- Zero "unknown identifier" errors
- Every lemma traceable to toolkit or existing code
- Lake build succeeds completely

## REMEMBER:
**This is 90% copy-paste work.** We have done the hard work already. Your job is to:
1. Find the right existing code
2. Verify lemma names
3. Copy patterns exactly
4. No creativity - just careful verification and copying