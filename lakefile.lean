import Lake
open Lake DSL

abbrev linterOptions : Array LeanOption := #[
  ⟨`linter.flexible, true⟩,
  ⟨`linter.oldObtain, true⟩,
  ⟨`linter.style.cdot, true⟩,
  ⟨`linter.style.dollarSyntax, true⟩,
  ⟨`linter.style.missingEnd, true⟩,
  ⟨`linter.style.lambdaSyntax, true⟩,
  ⟨`structureDiamondWarning, true⟩
]

package «Lean by Example» where
  keywords := #["manual", "reference", "tutorial", "japanese", "cheatsheet"]
  description := "プログラミング言語であるとともに定理証明支援系でもある Lean 言語と、その主要なライブラリの使い方を豊富なコード例とともに解説した資料です。"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ] ++ linterOptions.map (fun s ↦ {s with name := `weak ++ s.name})
  moreServerOptions := linterOptions

require «mk-exercise» from git
  "https://github.com/Seasawher/mk-exercise.git" @ "main"

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib LeanByExample where
  -- `lake build` の実行時にビルドされるファイルの設定
  -- `.submodules` と指定すると、そのディレクトリ以下の全ての Lean ファイルがビルドされる
  globs := #[.submodules `LeanByExample.Reference, .submodules `LeanByExample.Tutorial.Solution]

section Script

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

syntax (name := with_time) "with_time" "running" str doElem : doElem

macro_rules
  | `(doElem| with_time running $s $x) => `(doElem| do
    let start_time ← IO.monoMsNow;
    $x;
    let end_time ← IO.monoMsNow;
    IO.println s!"Running {$s}: {end_time - start_time}ms")

/-- mk_exercise と mdgen と mdbook を順に実行し、
Lean ファイルから Markdown ファイルと HTML ファイルを生成する。

`.\scripts\Build.ps1` を実行したほうが高速 -/
script build do
  with_time running "mk_exercise"
    runCmd "lake exe mk_exercise LeanByExample/Tutorial/Solution LeanByExample/Tutorial/Exercise"

  with_time running "mdgen"
    runCmd "lake exe mdgen LeanByExample booksrc"

  with_time running "mdbook"
    runCmd "mdbook build"
  return 0

end Script
