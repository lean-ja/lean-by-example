import Mathlib.Tactic.ByContra


-- ANCHOR: first
example (h: ¬Q → ¬P) : P → Q := by
  -- `P` であると仮定する
  intro hP

  -- `¬Q` であると仮定して矛盾を導きたい
  by_contra hnQ
  show False

  -- `¬ Q → ¬ P` と `¬Q` から `¬P` が導かれる
  have := h hnQ

  -- これは仮定に矛盾
  contradiction
-- ANCHOR_END: first