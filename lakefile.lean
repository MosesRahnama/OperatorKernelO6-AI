import Lake
open Lake DSL

package «OperatorKernelO6» where
  -- 1️⃣  Turn every warning or ‘sorry’ into a hard error
  moreLeanArgs := #[
    "-DwarningAsError=true",
    "-DsorryAsError=true"
  ]

@[default_target]                        -- 2️⃣  Make this the target ‘lake build’ checks
lean_lib «OperatorKernelO6» where
  -- 3️⃣  Tell Lake to compile every sub-module under this folder
  roots := #[`OperatorKernelO6]          -- adjust to your top-level namespace
  globs := #[.submodules `OperatorKernelO6]

-- Optional: if Termination.lean lives at the repo root:
lean_lib Termination where
  roots := #[`Termination]
  globs := #[`Termination]
