import Mathlib.Tactic.Linarith
import Std.Tactic.Omega

variable (a b : Nat)

example (h : (a - b : Int) ≤ 0) : (a - b = 0) := by
  -- `linarith` では示すことができません
  try linarith

  -- `omega` では示すことができます
  omega

example (h : a > 0) : (a - 1) + 1 = a := by
  try linarith
  omega

example (h : a / 2 < b) : a < 2 * b := by
  try linarith
  omega

example : (a - b) - b = a - 2 * b := by
  try linarith
  omega
