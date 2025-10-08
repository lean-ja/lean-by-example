import LeanByExample.Declarative.Syntax.Parser

/-- `parseArith` 関数の構成のために使われた、
`importModules` を使って Environment を一度保存するテクニックが
コンパイル時にも動作することを保証するためのテスト -/
def main : IO Unit := do
  let strings := ["1 + 2", "3 + (4 * 5)", "(1 + 2) * (3 + 4)"]
  for input in strings do
    let parsed := parseArith input
    match parsed with
    | .error e => throw <| IO.userError s!"Failed to parse '{input}': {e}"
    | .ok _expr => IO.println s!"Parsed '{input}'"
