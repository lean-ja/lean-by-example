import Mathlib.Tactic.Linarith

import Std.Data.Rat

variable (x y z : ℚ)

-- ANCHOR: first
example (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0): 12 * y - 4 * z ≥ 0 := by
  linarith
-- ANCHOR_END: first