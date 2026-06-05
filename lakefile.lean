import Lake
import Std

open Lake DSL

package «Lean by Example» where
  keywords := #["manual", "reference", "japanese"]
  description := "プログラミング言語であるとともに定理証明支援系でもある Lean 言語と、その主要なライブラリの使い方を豊富なコード例とともに解説した資料です。"
  leanOptions := #[]

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

open IO Process

def getOutput (input : String) (stdIn : Option String := none) : IO Output := do
  let cmdList := input.splitOn " "
  let cmd := cmdList.head!
  let args := cmdList.tail |>.toArray
  let out ← IO.Process.output
    (args := {cmd := cmd, args := args})
    (input? := stdIn)
  return out

def runCmd (input : String) : IO Unit := do
  let out ← getOutput input
  if out.stdout.trimAscii != "" then
    IO.println out.stdout

/-- mdgen と mdbook を順に実行し、
Lean ファイルから Markdown ファイルと HTML ファイルを生成する。-/
script build do
  runCmd "lake exe mdgen LeanByExample booksrc --count --exercise"
  runCmd "lake exe mdgen Exe booksrc"
  runCmd "mdbook build"

  -- SEO用のメタデータの更新。ローカルでは動作させる必要がないが、CI上では実行するべき
  runCmd "node scripts/updateSeoMetadata.mjs"
  return 0

end BuildScript

section TestScript

lean_exe prove_valid where
  root := `LeanByExample.TypeClass.GetElem.ProveValidExe

lean_exe parse where
  root := `LeanByExample.Declarative.Syntax.ParseExe
  supportInterpreter := true -- これがないとエラーになる

@[test_driver]
script test do
  runCmd "lake exe prove_valid"
  runCmd "lake exe parse"
  return 0

end TestScript
