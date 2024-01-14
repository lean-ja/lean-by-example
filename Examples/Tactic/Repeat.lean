/- # repeat

`repeat` は，指定したタクティクを失敗するまで繰り返します． -/
import Std.Tactic.SolveByElim -- `apply_assumption` のために必要

variable (P Q R S T : Prop)

example : (P → Q) → (Q → R) → (R → S) → (S → T) → P → T := by
  repeat intro
  repeat apply_assumption
