import LeanByExample.Declarative.Syntax.Parser

instance : ToString Op where
  toString := fun op =>
    match op with
    | Op.add => "+"
    | Op.mul => "*"

/-- `Arith`を文字列化する。ただし、全体を括弧で囲う。-/
protected def Arith.toStringAux (arith : Arith) : String :=
  match arith with
  | Arith.val n => toString n
  | Arith.app op lhs rhs =>
    "(" ++ Arith.toStringAux lhs ++ s!" {op} " ++ Arith.toStringAux rhs ++ ")"

protected def Arith.toString (arith : Arith) : String :=
  match arith with
  | Arith.val n => toString n
  | Arith.app op lhs rhs =>
    Arith.toStringAux lhs ++ s!" {op} " ++ Arith.toStringAux rhs

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
