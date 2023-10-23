import Mathlib.Tactic.Abel
import Mathlib.Tactic.WLOG

-- ANCHOR: first
example (a b : Nat) : a + b = b + a := by
  -- `a ≤ b` だと仮定しても一般性を失わない
  wlog h : a ≤ b with H

  -- `a ≤ b` なら成り立つと仮定して，そうでないときにも成り立つことを示す
  · show a + b = b + a
    guard_hyp H : ∀ (a b : Nat), a ≤ b → a + b = b + a
    guard_hyp h : ¬a ≤ b

    abel

  -- `a ≤ b` であるときに成り立つことを示す
  · show a + b = b + a
    guard_hyp h: a ≤ b

    abel
-- ANCHOR_END: first
