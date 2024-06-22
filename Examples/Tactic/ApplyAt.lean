/- # apply .. at

[`apply`](./Apply.md) は通常ゴールに対して適用しますが, `at` を付けてローカルコンテキストの命題などに対して使用するという使い方ができます．

実際にはこの構文は `apply` と似ているだけで，別のタクティクです．この `at` がついている構文は通常の `apply` とは異なり，後方推論ではなく前方推論になります．
-/
import Mathlib.Tactic.ApplyAt

variable (P Q : Prop)

example (h : P → Q) (hP : P) : Q := by
  -- `hP` に `h` を適用してしまう
  apply h at hP

  -- `hP` が書き換わる
  guard_hyp hP : Q

  assumption

/-! 便利な記法以上のものではなく，他のタクティクを利用しても同じことができます．-/

example (h : P → Q) (hP : P) : Q := by
  -- `apply at` は `replace` と同じように動作する
  replace hP := h hP

  -- `hP` が書き換わる
  guard_hyp hP : Q

  assumption
