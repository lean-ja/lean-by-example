import Lake
open Lake DSL

package examples {
  -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60autoImplicit.20true.60.20is.20evil/near/355145527
  moreLeanArgs := #["-DrelaxedAutoImplicit=false"]
  moreServerArgs := #["-DrelaxedAutoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "3ce43c18f614b76e161f911b75a3e1ef641620ff"

@[default_target]
lean_lib Examples {
  -- add lib config here
}
