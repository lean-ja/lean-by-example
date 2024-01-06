import Lake
open Lake DSL

package examples where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require «import-all» from git
  "https://github.com/Seasawher/import-all" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "ac94cca1865a06e5401a58746ed299936dacb312"

@[default_target]
lean_lib Examples where
  -- add lib config here
