import Mathlib.Tactic.Ring

variable (x y : Int)

-- ANCHOR: first
example : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
-- ANCHOR_END: first


-- ANCHOR: show_term
example : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  show_term ring
-- ANCHOR_END: show_term