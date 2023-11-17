import Mathlib.Tactic.ApplyAt -- `apply at` のため
import Std.Tactic.GuardExpr -- `guard_hyp` のため
import Std.Tactic.Replace -- `replace` のため

variable (P Q : Prop)

example (h : P → Q) (hP : P) : Q := by
  try
    -- `hP` に `h` を適用してしまう
    apply h at hP

    -- `hP` が書き換わる
    guard_hyp hP : Q

    fail

  -- `apply at` は `replace` と同じように動作する
  replace hP := h hP

  -- `hP` が書き換わる
  guard_hyp hP : Q

  assumption
