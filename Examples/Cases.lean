-- ANCHOR: first
example : P ∨ Q → (P → R) → (Q → R) → R := by
  -- `h: P ∨ Q`
  intro h hpr hqr

  -- `case inl` と `case inr` の２つのゴールを生成する
  cases h

  -- `P` が成り立つ場合
  case inl hp =>
    exact hpr hp

  -- `Q` が成り立つ場合
  case inr hq =>
    exact hqr hq
-- ANCHOR_END: first


-- ANCHOR: no_case
example : P ∨ Q → (P → R) → (Q → R) → R := by
  -- `h: P ∨ Q`
  intro h hpr hqr

  -- `case inl` と `case inr` の２つのゴールを生成する
  cases h with
  | inl hp =>
    exact hpr hp
  | inr hq =>
    exact hqr hq
-- ANCHOR_END: no_case