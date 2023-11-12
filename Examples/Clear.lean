import Mathlib.Tactic.ClearExcept -- `clear` タクティクで「～以外」を指定できるようにする

-- 未使用の変数に対する警告をオフにする
set_option linter.unusedVariables false

variable (P Q R : Prop)

example (hP : P) (hQ : Q) (hR : R) : R := by
  -- `hP` と `hR` 以外をローカルコンテキストから削除する
  clear * - hR hP

  -- `hP` も削除する
  clear hP

  exact hR
