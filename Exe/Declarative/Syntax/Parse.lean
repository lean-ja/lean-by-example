import LeanByExample.Declarative.Syntax.Parser

protected def Arith.toString (arith : Arith) : String :=
  match arith with
  | Arith.val n => toString n
  | Arith.app op lhs rhs =>
    let opStr :=
      match op with
      | Op.add => " + "
      | Op.mul => " * "
    "(" ++ Arith.toString lhs ++ opStr ++ Arith.toString rhs ++ ")"

instance : ToString Arith where
  toString := Arith.toString

/- `parseArith` 関数の構成のために使われた、
`importModules` を使って Environment を一度保存するテクニックが
コンパイル時にも動作することを保証するためのテスト -/
def main : IO Unit := do
  let strings := ["1 + 2", "3 + (4 * 5)", "(1 + 2) * (3 + 4)"]
  for input in strings do
    let parsed := parseArith input
    match parsed with
    | .error e => throw <| IO.userError s!"Failed to parse '{input}': {e}"
    | .ok expr => IO.println s!"Parsed '{input}', got {expr}"
