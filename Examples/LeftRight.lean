import Mathlib.Tactic

-- ANCHOR: first
example (hP: P) : P ∨ Q := by
  left
  assumption
-- ANCHOR_END: first


-- ANCHOR: without_math
example (hP: P) : P ∨ Q := by
  apply Or.inl
  assumption
-- ANCHOR_END: without_math