import Lake
open Lake DSL

package «Tactic Cheatsheet» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "v1.3.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0-rc1"

@[default_target]
lean_lib Examples where
  globs := #[.submodules `Examples]

def runCmd (cmd : String) (args : Array String) : ScriptM Bool := do
  let out ← IO.Process.output {
    cmd := cmd
    args := args
  }
  let hasError := out.exitCode != 0
  if hasError then
    IO.eprint out.stderr
  return hasError

script build do
  if ← runCmd "lake" #["exe", "mdgen", "Examples", "src"] then return 1
  if ← runCmd "mdbook" #["build"] then return 1
  return 0
