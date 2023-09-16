import Mathlib.Tactic


-- ANCHOR: first
example (h: ¬Q → ¬P) : P → Q := by
  -- `P` であると仮定する
  intro hP

  -- `¬Q` であると仮定する
  by_contra hnQ

  -- `¬ Q → ¬ P` と `¬Q` から `¬P` が導かれる
  have := h hnQ

  -- これは仮定に矛盾
  contradiction
-- ANCHOR_END: first