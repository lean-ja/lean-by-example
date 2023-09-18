import Mathlib.Tactic.LeftRight


-- ANCHOR: first
example (hP: P) : P ∨ Q := by
  left
  assumption
-- ANCHOR_END: first