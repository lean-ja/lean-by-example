import Lake
open Lake DSL

package examples {
  -- add configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

lean_lib Examples {
  -- add lib config here
}
