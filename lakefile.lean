import Lake
open Lake DSL

package OperatorKernelO6 where
  -- Focus on diagnostics options
  moreLeanArgs := #[
  "-Dpp.notation=true",
  -- "-Dtrace.Meta.Tactic.simp.rewrite=true",
  -- "-Dpp.proofs=true",
  -- "-Dpp.explicit=true",
  "-Dtrace.profiler.threshold=5"
  ]

@[default_target]
lean_lib OperatorKernelO6 where
  roots := #[`OperatorKernelO6]
  globs := #[.submodules `OperatorKernelO6]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"

lean_exe OperatorKernelO6Exe where
  root := `Main
