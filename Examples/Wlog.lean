import Mathlib.Tactic.Abel -- `abel` のために必要
import Mathlib.Tactic.WLOG -- `wolog` のために必要

variable (a b : ℕ)

example : a + b = b + a := by
  -- `a ≤ b` だと仮定しても一般性を失わない
  wlog h : a ≤ b with H

  case inr =>
    -- `a ≤ b` なら成り立つと仮定して，そうでないときにも成り立つことを示す
    guard_hyp H : ∀ (a b : Nat), a ≤ b → a + b = b + a
    guard_hyp h : ¬a ≤ b
    show a + b = b + a

    abel

  -- `a ≤ b` であるときに成り立つことを示す
  show a + b = b + a
  guard_hyp h: a ≤ b

  abel
