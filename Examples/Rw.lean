import Mathlib.Algebra.Group.Basic -- 群の定義を import する
import Mathlib.Tactic.NthRewrite -- `nth_rw` のために必要

/-! ## rw -/

example (a b c d e f : ℕ) (h : a * b = c * d) (h' : e = f) :
    a * (b * e) = c * (d * f) := by
  rw [h']

  -- 結合法則を使う
  rw [← Nat.mul_assoc]
  rw [h]

  -- 結合法則を使う
  rw [Nat.mul_assoc]

/-!
  ## nth_rw

  `rw` はマッチした項をすべて置き換えてしまいます．
  特定の項だけを書き換えたいとき，`nth_rw` が使用できます．
  対象の式中に現れる順番を1始まりで指定することで，項を指定します．
-/

-- `G` は群
variable (G : Type) [Group G]

example (a b : G) : a * b⁻¹ = 1 ↔ a = b := by

  -- `one_mul: 1 * b = b` を使って `b` を `1 * b` に書き換えたい
  try (
    -- 仮に普通に `rw` しようとすると…
    rw [← one_mul b]

    -- 左側にある `b` まで一緒に置き換わってしまった！
    show a * (1 * b)⁻¹ = 1 ↔ a = 1 * b

    -- これは失敗
    fail
  )

  -- `b` は2回出現するが，2番目だけ置き換える
  nth_rw 2 [← one_mul b]

  -- `mul_inv_eq_iff_eq_mul: a * b⁻¹ = c ↔ a = c * b` を使う
  exact mul_inv_eq_iff_eq_mul
