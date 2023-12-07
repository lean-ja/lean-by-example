import Std.Tactic.GuardExpr -- `guard_hyp` を使うために必要

variable (P : Prop)

example (hP : P) : P := by
  -- 現在ローカルコンテキストにある命題を確認できる
  guard_hyp hP : P

  exact hP
