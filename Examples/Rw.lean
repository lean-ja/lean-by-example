import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.NthRewrite


-- ANCHOR: rw
example (a b c d e f : Nat) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']

  -- 結合法則を使う
  rw [← Nat.mul_assoc]
  rw [h]

  -- 結合法則を使う
  rw [Nat.mul_assoc]
-- ANCHOR_END: rw

-- ANCHOR: nth_rw
-- `G` は群
variable [Group G]

example (a b : G) : a * b⁻¹ = 1 ↔ a = b := by
  -- `one_mul: 1 * b = b` を使って `b` を `1 * b` に書き換える
  -- `b` は2回出現するが，2番目だけ置き換える
  nth_rw 2 [← one_mul b]

  -- `mul_inv_eq_iff_eq_mul: a * b⁻¹ = c ↔ a = c * b` を使う
  exact mul_inv_eq_iff_eq_mul
-- ANCHOR_END: nth_rw
