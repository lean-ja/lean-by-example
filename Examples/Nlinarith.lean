import Mathlib.Tactic.Linarith

-- ANCHOR: first
example (a b: Nat) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  -- `linarith` では示すことができない
  try linarith

  nlinarith
-- ANCHOR_END: first