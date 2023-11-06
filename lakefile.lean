import Lake
open Lake DSL

package examples {
  -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60autoImplicit.20true.60.20is.20evil/near/355145527
  moreLeanArgs := #["-DrelaxedAutoImplicit=false"]
  moreServerArgs := #["-DrelaxedAutoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "b6ec7450650a5945bf4244751be4a5cf1fee962f"

@[default_target]
lean_lib Examples {
  -- add lib config here
}
