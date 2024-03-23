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
  "https://github.com/leanprover-community/mathlib4.git" @ "2353c4e34ff225a3890f76ab6315d76584255c93"

@[default_target]
lean_lib Examples where
  -- add lib config here

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
  if ← runCmd "lake" #["exe", "import_all, "Examples"] then return 1
  if ← runCmd "mdbook" #["build"] then return 1
  return 0
