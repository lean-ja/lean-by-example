-- ANCHOR: first
example (P: Prop) : ¬¬P → P := by
  intro hnnP

  -- `P` が成り立つかどうかで場合分けする
  by_cases hP: P

  case inl =>
    -- `P` が成り立つとき
    assumption

  case inr =>
    -- `P` が成り立たないとき
    contradiction
-- ANCHOR_END: first