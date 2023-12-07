import Mathlib.Tactic.Linarith -- `linarith` や `nlinarith` を使うため

variable (a b : ℕ)

/-! ## nlinarith -/

example (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  -- `linarith` では示すことができない
  try linarith

  nlinarith
