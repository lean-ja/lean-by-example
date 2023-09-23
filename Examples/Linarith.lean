import Mathlib.Tactic.Linarith

import Std.Data.Rat

variable (x y z : ℚ)

-- ANCHOR: first
example (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0): 12 * y - 4 * z ≥ 0 := by
  linarith
-- ANCHOR_END: first


-- ANCHOR: id
example : id x ≤ x := by
  -- `linarith` で示すことはできない
  try linarith

  have : id x = x := rfl

  -- `id x = x` だと教えてあげると `linarith` で示せる
  linarith
-- ANCHOR_END: id