import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.NthRewrite

-- `G` は群
variable [Group G]

example (a b : G) : a * b⁻¹ = 1 ↔ a = b := by
  -- `one_mul: 1 * b = b` を使って `b` を `1 * b` に書き換える
  -- `b` は2回出現するが，2番目だけ置き換える
  nth_rewrite 2 [← one_mul b]

  -- `mul_inv_eq_iff_eq_mul: a * b⁻¹ = c ↔ a = c * b` を使う
  exact mul_inv_eq_iff_eq_mul