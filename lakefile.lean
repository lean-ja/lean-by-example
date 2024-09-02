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
  -- `lake build` の実行時にビルドされるファイルの設定
  -- `.submodules` と指定すると、そのディレクトリ以下の全ての Lean ファイルがビルドされる
  globs := #[.submodules `Examples]

section Script

/-- 与えられた文字列をシェルで実行する -/
@[inline] def runCmd (input : String) : IO Unit := do
  let cmdList := input.splitOn " "
  let cmd := cmdList.head!
  let args := cmdList.tail |>.toArray
  let out ← IO.Process.output {
    cmd  := cmd
    args := args
  }
  if out.exitCode != 0 then
    IO.eprintln out.stderr
    throw <| IO.userError s!"Failed to execute: {input}"
  else if !out.stdout.isEmpty then
    IO.println out.stdout

/-- mk_exercise を実行し、演習問題の解答に
解答部分を sorry に置き換えるなどの処理を施して演習問題ファイルを生成する。-/
script mk_exercise do
  runCmd "lake exe mk_exercise Examples/Solution Exercise"
  return 0

syntax (name := with_time) "with_time" "running" str doElem : doElem

macro_rules
  | `(doElem| with_time running $s $x) => `(doElem| do
    let start_time ← IO.monoMsNow;
    $x;
    let end_time ← IO.monoMsNow;
    IO.println s!"Running {$s}: {end_time - start_time}ms")

/-- mk_exercise と mdgen と mdbook を順に実行し、
Lean ファイルから Markdown ファイルと HTML ファイルを生成する。-/
script build do
  let start_time ← IO.monoMsNow;

  -- `lake run mk_exercise` を使用すると遅くなってしまうのでコピペしている
  with_time running "mk_exercise"
    runCmd "lake exe mk_exercise Examples/Solution Exercise"

  with_time running "mdgen"
    runCmd "lake exe mdgen Examples src";
    runCmd "lake exe mdgen Exercise src/Exercise"

  with_time running "mdbook"
    runCmd "mdbook build"

  let end_time ← IO.monoMsNow;
  IO.println s!"Total time: {end_time - start_time}ms"
  return 0

end Script
