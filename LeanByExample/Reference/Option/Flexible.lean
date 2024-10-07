import Mathlib.Tactic

set_option linter.flexible true

example {n m : Nat} (h : n + 0 = m) : True ∧ (n = m) := by
  constructor
  all_goals
    simp_all
