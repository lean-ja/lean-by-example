import Lake
open Lake DSL

package examples where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "ac94cca1865a06e5401a58746ed299936dacb312"

@[default_target]
lean_lib Examples where
  -- add lib config here

@[default_target]
lean_exe importAll where
  root := `scripts.importAll
  supportInterpreter := true
