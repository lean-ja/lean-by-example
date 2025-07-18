import Playground.PIH.Chapter09.Section6

/-- インタプリンタでは重いのでコンパイラで実行 -/
def main : IO Unit :=
  let result := Expr.solutions [1, 3, 7, 10, 25, 50] 765
  IO.println result
