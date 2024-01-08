import Lake
open Lake DSL

package examples where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require «import-all» from git
  "https://github.com/Seasawher/import-all" @ "main"

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "526457f3dc192dd9195993e0a48c9374b81af9c7"

@[default_target]
lean_lib Examples where
  -- add lib config here
