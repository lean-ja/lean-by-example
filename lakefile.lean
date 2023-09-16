import Lake
open Lake DSL

package examples {
  -- add configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "96806534a3a47c26cec8985be643f13c2a1b9c92"

lean_lib Examples {
  -- add lib config here
}
