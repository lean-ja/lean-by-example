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

@[inline]
def runCmd (cmd : String) (args : Array String) : ScriptM Bool := do
  let out ← IO.Process.output {
    cmd := cmd
    args := args
  }
  let hasError := out.exitCode != 0
  if hasError then
    IO.eprint out.stderr
  return hasError

/-- mk_exercise を実行し、演習問題の解答に
解答部分を sorry に置き換えるなどの処理を施して演習問題ファイルを生成する。-/
script mk_exercise do
  if ← runCmd "lake" #["exe", "mk_exercise", "Examples/Solution", "Examples/Exercise"] then return 1
  return 0

@[inline]
macro "with_time" x:doElem : doElem => `(doElem| do
  let start_time ← IO.monoMsNow;
  $x;
  let end_time ← IO.monoMsNow;
  IO.println s!"{end_time - start_time}ms")

/-- mk_exercise と mdgen と mdbook を順に実行し、
Lean ファイルから Markdown ファイルと HTML ファイルを生成する。-/
script build do
  -- `lake run mk_exercise` を使用すると遅くなってしまうのでコピペしている
  IO.print "Running mk_exercise: "
  with_time if ← runCmd "lake" #["exe", "mk_exercise", "Examples/Solution", "Examples/Exercise"] then return 1

  IO.print "Running mdgen: "
  with_time if ← runCmd "lake" #["exe", "mdgen", "Examples", "src"] then return 1

  IO.print "Running mdbook: "
  with_time if ← runCmd "mdbook" #["build"] then return 1

  return 0
