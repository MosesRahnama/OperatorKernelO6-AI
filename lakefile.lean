import Lake
open Lake DSL

package «OperatorKernelO6» where
  -- Package configuration goes inside this block
  moreLeanArgs := #[
    "--warning_as_error", "declaredAsImport", "declaredMultipleTimes",
    "-Ddiagnostics.errors=true",
    "-Dtrace.Meta.Tactic=true",
    "-Dtrace.Meta.debug=true",
    "-Dpp.proofs=true",
    "-Ddiagnostics.showGoals=true",
    "-Dlinter.all=true",        -- Enable all linters
    "-Dtactic.proofRecErrorTolerance=0",  -- Important! Makes proof errors fail compilation
    "-Dtactic.hygiene=false"   -- Don't require all variables to be used
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
