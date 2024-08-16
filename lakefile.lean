import Lake
open Lake DSL

package «Lean by Example» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require «mk-exercise» from git
  "https://github.com/Seasawher/mk-exercise.git" @ "main"

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

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
  if ← runCmd "lake" #["exe", "mk_exercise", "Examples/Solution", "Examples/Exercise"] then return 1
  if ← runCmd "lake" #["exe", "mdgen", "Examples", "src"] then return 1
  if ← runCmd "mdbook" #["build"] then return 1
  return 0

script link_test do
  if ← runCmd "lychee" #["--base", "book", "."] then return 1
  return 0
