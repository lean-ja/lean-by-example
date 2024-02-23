/- # rw

`rw` は rewrite（書き換え）を行うタクティクです．等式や同値をもとに書き換えを行います．

`hab: a = b` や `hPQ : P ↔ Q` がローカルコンテキストにあるとき，

* `rw [hab]` はゴールの中の `a` をすべて `b` に置き換え，
* `rw [hPQ]` はゴールの中の `P` をすべて `Q` に置き換えます．

順番は重要で，`b` を `a` に置き換えたいときなどは `rw [← hab]` のように `←` をつけます．

`h1, h2, ...` について続けて置き換えを行いたいときは，`rw [h1, h2, ...]` のようにします．

ゴールではなく，ローカルコンテキストにある `h: P` を書き換えたいときには `at` をつけて `rw [hPQ] at h` とします．すべての箇所で置き換えたいときは `rw [hPQ] at *` とします． -/
import Mathlib.Algebra.Group.Basic -- 群の定義を import する
import Mathlib.Tactic.NthRewrite -- `nth_rw` のために必要 --#

example (a b c d e f : ℕ) (h : a * b = c * d) (h' : e = f) :
    a * (b * e) = c * (d * f) := by
  rw [h']

  -- 結合法則を使う
  rw [← Nat.mul_assoc]
  rw [h]

  -- 結合法則を使う
  rw [Nat.mul_assoc]

/-! ## nth_rw

`rw` はマッチした項をすべて置き換えてしまいます．
特定の項だけを書き換えたいとき，`nth_rw` が使用できます．
対象の式中に現れる順番を1始まりで指定することで，項を指定します．

これには `Mathlib.Tactic.NthRewrite` の import が必要です．
-/

-- `G` は群
variable (G : Type) [Group G]

example (a b : G) : a * b⁻¹ = 1 ↔ a = b := by

  -- `one_mul: 1 * b = b` を使って `b` を `1 * b` に書き換えたい
  try
    -- 仮に普通に `rw` しようとすると…
    rw [← one_mul b]

    -- 左側にある `b` まで一緒に置き換わってしまった！
    show a * (1 * b)⁻¹ = 1 ↔ a = 1 * b

    -- これは失敗
    fail

  -- `b` は2回出現するが，2番目だけ置き換える
  nth_rw 2 [← one_mul b]

  -- `mul_inv_eq_iff_eq_mul: a * b⁻¹ = c ↔ a = c * b` を使う
  exact mul_inv_eq_iff_eq_mul

/-! ## rewrite

`rewrite` というタクティクもあります．`rw` とよく似ていて，違いは `rw` が書き換え後に自動的に `rfl` を実行するのに対して，`rewrite` は行わないということです．-/
