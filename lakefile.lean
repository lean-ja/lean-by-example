import Lake
open Lake DSL

package «Lean by Example» where
  keywords := #["manual", "reference", "japanese"]
  description := "プログラミング言語であるとともに定理証明支援系でもある Lean 言語と、その主要なライブラリの使い方を豊富なコード例とともに解説した資料です。"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib LeanByExample where
  -- `lake build` の実行時にビルドされるファイルの設定
  -- `.submodules` と指定すると、そのディレクトリ以下の全ての Lean ファイルがビルドされる
  globs := #[.submodules `LeanByExample]

section BuildScript

/-- 与えられた文字列をシェルで実行する -/
def runCmd (input : String) : IO Unit := do
  let cmdList := input.splitOn " "
  let cmd := cmdList.head!
  let args := cmdList.tail |>.toArray
  let out ← IO.Process.output {
    cmd := cmd
    args := args
  }
  if out.exitCode != 0 then
    IO.eprintln out.stderr
    throw <| IO.userError s!"Failed to execute: {input}"
  else if !out.stdout.isEmpty then
    IO.println out.stdout

/-- mdgen と mdbook を順に実行し、
Lean ファイルから Markdown ファイルと HTML ファイルを生成する。-/
script build do
  runCmd "lake exe mdgen LeanByExample booksrc --count"
  runCmd "lake exe mdgen Exe booksrc"
  runCmd "mdbook build"
  return 0

end BuildScript


section TestScript

lean_exe get_elem where
  root := `Exe.TypeClass.GetElem.ProveValid

lean_exe parse where
  root := `Exe.Declarative.Syntax.Parse
  supportInterpreter := true -- これがないとエラーになる

def runCmdWithOutput (input : String) : IO String := do
  let cmdList := input.splitOn " "
  let cmd := cmdList.head!
  let args := cmdList.tail |>.toArray
  let out ← IO.Process.output {
    cmd := cmd
    args := args
  }
  unless out.exitCode == 0 do
    IO.eprintln out.stderr
    throw <| IO.userError s!"Failed to execute: {input}"

  return out.stdout

/-- `Type/IO/Cat.lean`のためのテスト -/
def testForCat : IO Unit := do
  let result ← runCmdWithOutput "lean --run LeanByExample/Type/IO/Cat.lean LeanByExample/Type/IO/Test.txt"
  let expected := "Lean is nice!"
  if result.trim != expected then
    throw <| IO.userError s!"Test failed! expected: {expected}, got: {result.trim}"

/-- `Type/IO/Greet.lean`のためのテスト -/
def testForGreet : IO Unit := do
  let result ← runCmdWithOutput "lean --run LeanByExample/Type/IO/Greet.lean"
  let expected := "誰に挨拶しますか？\nHello, !"
  if result.trim != expected then
    throw <| IO.userError s!"Test failed! expected prefix: {expected}, got: {result}"

@[test_driver]
script test do
  runCmd "lake exe get_elem"
  runCmd "lake exe parse"
  testForCat
  testForGreet
  return 0

end TestScript
