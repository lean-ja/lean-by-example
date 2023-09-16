-- ANCHOR: without_math
example (hP: P) : P ∨ Q := by
  apply Or.inl
  exact hP
-- ANCHOR_END: without_math