import Mathlib.Tactic.Linarith -- `linarith` のために必要
import Mathlib.Util.Time -- `#time` を使うため
import Std.Data.Rat.Basic -- `ℚ` のために必要

variable (x y z : ℚ)

/-! ## linarith -/

example (h1: x = 2 * y) (h2 : - x + 2 * y = 1) : False := by
  linarith

example (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) :
    12 * y - 4 * z ≥ 0 := by
  linarith

-- 利用できる命題を増やすことで，通るようになることがある
example : id x ≤ x := by
  -- `linarith` で示すことはできない
  try linarith

  have : id x = x := rfl

  -- `id x = x` だと教えてあげると `linarith` で示せる
  linarith

/-! ## linarith と他のタクティクの使い分け
  `1 < 2` のような簡単な数値のみの不等式の場合，
  `norm_num` や `simp_arith` でも証明ができます．
  しかし，コマンド実行にかかる時間に違いがあります．
-/

-- 実行環境により正確な実行時間は異なりますが，
-- `linarith` は比較的重いタクティクです

#time example : 1 < 2 := by simp_arith

#time example : 1 < 2 := by norm_num

#time example : 1 < 2 := by linarith
