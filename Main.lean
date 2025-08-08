import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Meta
-- import OperatorKernelO6.Meta.Termination
import OperatorKernelO6.Meta.Termination_C
import OperatorKernelO6.Meta.Termination_Lex

-- import LeanSearchClient  -- Enable search commands (temporarily disabled)
-- import OperatorKernelO6.Meta.Arithmetic
-- import OperatorKernelO6.Meta.Equality
-- import OperatorKernelO6.Meta.Godel
-- import OperatorKernelO6.Meta.Normalize
-- import OperatorKernelO6.Meta.FixedPoint
-- import OperatorKernelO6.Meta.Confluence
-- import OperatorKernelO6.Meta.ProofSystem

open OperatorKernelO6
open MetaSN

-- Example of search-first development workflow:
-- Before writing any theorem, search for existing definitions
-- #search "ordinal addition"  -- (disabled until LeanSearchClient is working)

/-- GREEN-CHANNEL: Demonstration of search-first workflow --/
example : ∀ n : ℕ, n + 0 = n := by
  intro n
  rfl  -- This should work since it's basic arithmetic

-- -- Add a deliberate error to test if settings work
-- theorem test_error : 2 + 2 = 5 := by
--   sorry -- This should cause the build to fail

def main (args : List String) : IO UInt32 := do
  IO.println "OperatorKernelO6 loaded successfully"
  IO.println "Search-first development workflow enabled"
  return 0
