/- # rw_search

`rw_search` は，ゴールが等式であるときに，ライブラリにある命題を使って `rw` することを繰り返し，そのゴールを閉じようとするタクティクです．-/
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

/- `rw` では同値関係も扱うことができますが，`rw_search` が扱うのは等式のみです． -/

/-- error: Goal is not an equality. -/
#guard_msgs in example (h : n + m = 0) : n = 0 ↔ m = 0 := by
  -- ゴールが等式でないのでエラーになる
  rw_search

-- `=` に書き換えると何故か示せる
example (h : n + m = 0) : n = 0 ↔ m = 0 := by
  suffices (n = 0) = (m = 0) from Eq.to_iff this

  rw_search says
    rw [propext (eq_zero_iff_eq_zero_of_add_eq_zero h)]

/-! ## rw?
`rw?` は `apply?` のように，ゴールを `rw` できる補題をライブラリから検索します．`rw?` は等式以外も扱うことができます．-/

example (h : n + m = 0) : n = 0 ↔ m = 0 := by
  -- 複数の候補を出してしまうが，候補は出してくれる
  rw?

  sorry
