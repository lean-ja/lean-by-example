-- ANCHOR: first
example : P ∨ Q → (P → R) → (Q → R) → R := by
  -- `h: P ∨ Q`
  intro h hPR hQR

  -- `case inl` と `case inr` の２つのゴールを生成する
  cases h

  -- `P` が成り立つ場合
  case inl hP =>
    exact hPR hP

  -- `Q` が成り立つ場合
  case inr hQ =>
    exact hQR hQ
-- ANCHOR_END: first


-- ANCHOR: no_case
example : P ∨ Q → (P → R) → (Q → R) → R := by
  -- `h: P ∨ Q`
  intro h hPR hQR

  -- `case inl` と `case inr` の２つのゴールを生成する
  cases h with
  | inl hP =>
    exact hPR hP
  | inr hQ =>
    exact hQR hQ
-- ANCHOR_END: no_case