import Playground.PIH.Ch09.S04

/-- 与えられた式 `expr : Expr` が `inputs` と `target` の定義する
カウントダウン問題の解になっているかどうか判定する -/
def Expr.solution (expr : Expr) (inputs : List Pos) (target : Pos) : Bool :=
  expr.eval == some target && inputs.choices.contains expr.values

-- 式 `1 + (2 * 3)` は `inputs := [1, 2, 3, 8, 13]` と
-- `target := 7` で定義される問題の解になっている
#guard expr!{1 + 2 * 3}.solution [1, 2, 3, 8, 13] 7

#guard expr!{(25 - 10) * (1 + 50)}.solution [1, 3, 7, 10, 25, 50] 765
