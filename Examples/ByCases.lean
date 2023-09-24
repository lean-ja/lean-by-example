import Std.Tactic.GuardExpr

-- ANCHOR: first
example (P: Prop) : ¬¬P → P := by
  intro hnnP

  -- `P` が成り立つかどうかで場合分けする
  by_cases hP: P

  case inl =>
    -- `P` が成り立つとき
    guard_hyp hP : P

    assumption

  case inr =>
    -- `¬ P` が成り立つとき
    guard_hyp hP : ¬P

    contradiction
-- ANCHOR_END: first