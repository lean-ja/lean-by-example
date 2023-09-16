-- ANCHOR: without_math
example (hP: P) : P ∨ Q := by
  apply Or.inl
  assumption
-- ANCHOR_END: without_math