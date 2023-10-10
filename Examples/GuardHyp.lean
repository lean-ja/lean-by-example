import Std.Tactic.GuardExpr

-- ANCHOR: first
example (hP : P) : P := by
  -- 現在ローカルコンテキストにある命題を確認できる
  guard_hyp hP : P

  exact hP
-- ANCHOR_END: first