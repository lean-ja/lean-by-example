import Mathlib.Tactic.Linarith

variable (a b : ℕ)

/-! ## nlinarith -/

example (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  -- `linarith` では示すことができない
  try linarith

  nlinarith
