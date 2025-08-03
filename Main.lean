import OperatorKernelO6.Kernel
import OperatorKernelO6.Meta.Termination

open OperatorKernelO6
open MetaSN

-- -- Add a deliberate error to test if settings work
-- theorem test_error : 2 + 2 = 5 := by
--   sorry -- This should cause the build to fail

def main (args : List String) : IO UInt32 := do
  IO.println "OperatorKernelO6 loaded successfully"
  return 0
