import Mathlib.Tactic.GCongr

variable (a b c d: Nat)

-- ANCHOR: first
example (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  rel [h1, h2]
-- ANCHOR_END: first


-- ANCHOR: guess
example (x: Int) (h1 : a ≤ b) : x ^ 2 * a ≤ x ^ 2 * b := by
  rel [h1]
-- ANCHOR_END: guess