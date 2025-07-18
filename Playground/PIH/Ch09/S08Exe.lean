import Playground.PIH.Ch09.S08

/-- インタプリンタでは重いのでコンパイラで実行 -/
def main : IO Unit := do
  let start_time ← IO.monoMsNow
  let result := Expr.solutions [1, 3, 7, 10, 25, 50] 765
  IO.println result
  let end_time ← IO.monoMsNow
  IO.println s!"time: {end_time - start_time}ms"

#eval main
