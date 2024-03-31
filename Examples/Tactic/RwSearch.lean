/- # rw_search

`rw_search` は，ゴールが等式であるときに，ライブラリにある命題を使って `rw` することを繰り返し，そのゴールを閉じようとするタクティクです．

`rw` では同値関係も扱うことができますが，`rw_search` が扱うのは等式のみです．-/
import Mathlib.Tactic.RewriteSearch -- `rw_search` のために必要
import Mathlib.Tactic.Ring -- `ring` のために必要

variable (m n : ℕ)

-- `says` のチェックを有効にする
set_option says.verify true

example : (m - n) - n = m - 2 * n := by
  -- `ring` では示せない．自然数は環ではないので当然
  try ring

  -- `aesop` でも示せない
  fail_if_success aesop

  rw_search says
    rw [Nat.sub_sub, Nat.mul_two]

/-! ## rw?
`rw?` は `apply?` のように，ゴールを `rw` できる補題をライブラリから検索します．`rw?` は等式以外も扱うことができます．-/

example (h : n + m = 0) : n = 0 ↔ m = 0 := by
  -- ゴールは等式ではありませんと言われてエラーになる
  fail_if_success rw_search

  rw? says
    rw [propext (eq_zero_iff_eq_zero_of_add_eq_zero h)]
