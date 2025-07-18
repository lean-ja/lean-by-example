import Playground.PIH.Chapter13.Section7

open Parser

mutual
  /-- 式のパーサ -/
  partial def expr : Parser Nat := do
    let t ← term
    let tail : Parser Nat := do
      let _ ← symbol "+"
      let e ← expr
      return t + e
    tail <|> return t

  /-- 項のパーサ -/
  partial def term : Parser Nat := do
    let f ← factor
    let tail : Parser Nat := do
      let _ ← symbol "*"
      let t ← term
      return f * t
    tail <|> return f

  /-- 因子のパーサ -/
  partial def factor : Parser Nat := do
    let first : Parser Nat := do
      let _ ← symbol "("
      let e ← expr
      let _ ← symbol ")"
      return e
    first <|> natural

end

/-- 文字列として与えられた式をパースして評価する -/
def eval (input : String) : Nat :=
  match expr input with
  | some (n, ⟨[]⟩) => n
  | some (_, _) => panic! "Unused input remains"
  | none => panic! "invalid input"

#guard eval "2*3+4" = 10

#guard eval "2*(3+4)" = 14
