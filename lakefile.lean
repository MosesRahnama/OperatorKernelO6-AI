-- import Lake
-- open Lake DSL

-- -- package «OperatorKernelO6» where
-- --   -- Package configuration goes inside this block
-- --   moreLeanArgs := #[
-- --     -- Remove the problematic warning flags
-- --     "-Ddiagnostics.errors=true",
-- --     "-Dpp.proofs=true",
-- --     "-Ddiagnostics.showGoals=true",
-- --     "-Dlinter.all=true",        -- Enable all linters
-- --     "-Dtactic.proofRecErrorTolerance=0",  -- Important! Makes proof errors fail compilation
-- --     "-Dtactic.hygiene=false"   -- Don't require all variables to be used
-- --   ]

-- -- Add this lean_lib declaration to ensure your module is built with proper settings
-- @[default_target]
-- lean_lib OperatorKernelO6 where
--   -- This ensures the module gets proper error reporting
--   leanOptions := #[
--     ⟨`tactic.proofRecErrorTolerance, .ofNat 0⟩  -- Make errors fail compilation
--   ]

-- require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
