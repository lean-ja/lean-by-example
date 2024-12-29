/- # rw_search

`rw_search` は、ゴールが等式であるときに、ライブラリにある命題を使って `rw` することを繰り返し、そのゴールを閉じようとするタクティクです。-/
import Mathlib.Tactic.RewriteSearch -- `rw_search` のために必要
import Mathlib.Tactic.Ring -- `ring` のために必要

variable (m n : ℕ)

-- `says` のチェックを有効にする
set_option says.verify true

example : (m - n) - n = m - 2 * n := by
  -- `ring` では示せない。自然数の引き算は環の公理を満たさないから
  fail_if_success solve
  | ring

  -- `aesop` でも示せない
  fail_if_success aesop

  rw_search says
    rw [Nat.sub_sub, Nat.two_mul]

/- `rw` では同値関係も扱うことができますが、`rw_search` が扱うのは等式のみです。 -/

/-- error: Goal is not an equality. -/
#guard_msgs in example (h : n + m = 0) : n = 0 ↔ m = 0 := by
  -- ゴールが等式でないのでエラーになる
  rw_search

-- `=` に書き換えると示せる
example (h : n + m = 0) : n = 0 ↔ m = 0 := by
  suffices (n = 0) = (m = 0) from Eq.to_iff this

  rw_search says
    rw [propext (eq_zero_iff_eq_zero_of_add_eq_zero h)]

/- ## rw?
`rw?` は `apply?` のように、ゴールを `rw` できる補題をライブラリから検索します。`rw?` は等式以外も扱うことができますが、`rw_search` と同様に同値関係の扱いは苦手です。-/
set_option linter.unusedTactic false in --#

example (h : n + m = 0) : n = 0 ↔ m = 0 := by
  try
    -- 複数の候補を出してしまうが、候補は出してくれる
    rw?

    -- いったん失敗させる
    fail

  -- `=` に書き換えると一発で示せる
  suffices (n = 0) = (m = 0) from Eq.to_iff this
  rw? says
    rw [propext (eq_zero_iff_eq_zero_of_add_eq_zero h)]
