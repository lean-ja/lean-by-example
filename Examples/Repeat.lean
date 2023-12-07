import Mathlib.Tactic.SolveByElim

variable (P Q R S T : Prop)

example : (P → Q) → (Q → R) → (R → S) → (S → T) → P → T := by
  repeat intro
  repeat apply_assumption
