import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Says

variable (P Q R S: Prop)

-- ANCHOR: first
example (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  -- `exact?` は実行されない
  exact? says exact hRS (hQR (hPQ hP))
-- ANCHOR_END: first
