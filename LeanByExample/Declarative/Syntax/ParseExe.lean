/-
このファイルは `lake test` 時に実行されるだけで、読者からは見えない場所にあります
-/
import LeanByExample.Lib.ThisFile
import LeanByExample.Declarative.Syntax.Parser

/- `parseArith` 関数の構成のために使われた、
`importModules` を使って Environment を一度保存するテクニックが
`lake exe` コマンドで実行した時にも動作することを保証するためのテスト -/
def main : IO Unit := do
  let strings := ["1 + 2", "3 + (4 * 5)", "(1 + 2) * (3 + 4)"]
  let mut hasError := false
  for input in strings do
    let parsed := parseArith input
    if let .error _e := parsed then
      hasError := true

  if hasError then
    throw <| .userError "Failed to parse some arithmetic expressions."
  IO.println s!"✅ [{this_file%}] テスト成功"
