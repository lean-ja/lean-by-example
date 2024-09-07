/- # linarith

`linarith` は線形算術(linear arithmetic)を行うタクティクです。Fourier-Motzkin elimination を用いて、線形な(不)等式系から矛盾を導こうとします。一般に、ゴールが `False` でないときにはゴールの否定を仮定に加えることで、ゴールを閉じようとします。 -/
import Mathlib.Tactic.Linarith -- `linarith` のために必要
import Batteries.Data.Rat.Basic -- `ℚ` のために必要

variable (x y z : ℚ)

example (h1: x = 2 * y) (h2 : - x + 2 * y = 1) : False := by
  linarith

example (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) :
    12 * y - 4 * z ≥ 0 := by
  linarith

/-! `linarith` はローカルコンテキストにある命題を読むので、`linarith` が通らないとき、追加で補題を示すことで解決することがあります。-/

example : id x ≤ x := by
  -- `linarith` で示すことはできない
  fail_if_success linarith

  have : id x = x := rfl

  -- `id x = x` だと教えてあげると `linarith` で示せる
  linarith

/- また、使ってほしい補題を直接渡すこともできます。-/

example (h : x ≤ y) (pos : 0 ≤ x) : x + x ^ 2 ≤ y + y ^ 2 := by
  -- `linarith` では示せない
  fail_if_success linarith

  -- `linarith` 単独で扱えない部分、つまり `x ^ 2 ≤ y ≤ 2` を示すための
  -- 補題を引数で渡してやると通る
  linarith [pow_le_pow_left pos h 2]

/- ## 舞台裏
`linarith` は一般に、型クラス `LinearOrderedCommRing` のインスタンスに対して動作します。ここで linear order とは全順序のことです。-/
section --#
variable {R : Type} [LinearOrderedCommRing R]

variable (x y z : R)

-- R 上の不等式だが `linarith` で証明できる
example (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) :
    12 * y - 4 * z ≥ 0 := by
  linarith

end --#
/-! ## linarith と他のタクティクの使い分け
`1 < 2` のような簡単な数値のみの不等式の場合、`norm_num` や `simp_arith` でも証明ができます。
同じ命題を示すのに複数のコマンドがあるわけですが、コマンド実行にかかる時間に違いがあります。

実行環境により正確な実行時間は異なりますが、`linarith` は比較的重いタクティクです。
-/

#time example : 1 < 2 := by simp_arith

#time example : 1 < 2 := by norm_num

#time example : 1 < 2 := by linarith
