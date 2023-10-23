import Mathlib.Tactic.SolveByElim

variable (P Q R : Prop)

-- ANCHOR: first
example (hPQ : P → Q) : ¬ Q → ¬ P := by
  intro hQn hP

  -- 矛盾を示したい
  show False

  -- 自動で `hQn` を適用
  apply_assumption
  show Q

  -- 自動で `hPQ` を適用
  apply_assumption
  show P

  -- 自動で `hP` を適用
  apply_assumption
  done
-- ANCHOR_END: first


-- ANCHOR: repeat
example (hPQ : P → Q) (hQR : Q → R) (hQ : P) : R := by
  repeat apply_assumption
-- ANCHOR_END: repeat
