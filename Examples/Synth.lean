import Mathlib.Data.Rat.Defs -- 有理数
import Mathlib.Data.Real.Basic -- 実数

/-! # synth コマンド -/

/-! ## 型クラスについて -/

-- `n` は自然数で，`x` は有理数
variable (n : ℕ) (x : ℚ)

-- `x` の逆数は定義できますが
#check x⁻¹

-- `n` の逆数は定義されていません.
-- 自然数は `Inv` のインスタンスではないというメッセージが出ます.
#check_failure n⁻¹

/-! ## synth コマンドの使い方 -/

-- `Real.instInvReal` と出力されます
#synth Inv Real

-- def Real.instInvReal : Inv ℝ :=
-- { inv := Real.inv' }
#print Real.instInvReal

-- `Nat` は `Inv` のインスタンスではないので，以下はエラーになります
-- コメントを外して確かめてみましょう
-- #synth Inv Nat
