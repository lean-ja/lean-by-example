/- # Float

`Float` は浮動小数点数を表す型です。

浮動小数点数は、おおざっぱには有限桁の小数のようなものであるといえます。
-/
import Batteries.Data.Rat.Basic --#
import Mathlib.Data.String.Defs --#

#eval (0.01 : Float)

#eval (-2.34 : Float)

#eval (-42.0 : Float)

/- ## 内部実装

浮動小数点数は、[IEEE 754](https://ja.wikipedia.org/wiki/IEEE_754) に従い内部的には符号 `s ∈ {0, 1}` と仮数(significand) `c : ℕ` と指数 `q : ℤ` の三つ組で表されています。これは `(-1)ˢ × c × 2 ^ q` として解釈されます。
-/

-- `64 = 1 * 2⁶` なので、仮数部は 1 で指数は 6 になる
#guard Float.toRatParts' 64.0 = some (1, 6)

-- `6 = 3 * 2¹` なので、仮数部は 3 で指数は 1 になる
#guard Float.toRatParts' 6.0 = some (3, 1)

-- `0.5 = 1 * 2⁻¹` なので、仮数部は 1 で指数は -1 になる
#guard Float.toRatParts' 0.5 = some (1, -1)

/- ## 誤差
特に、浮動小数点数は2進数として表現されているので、一般に `Float` で10進数を正確に計算することはできません。
次のように `0.1 : Float` を表示させると気が付きませんが、これは表示の際に数値が丸められているためです。
-/

/-- info: 0.100000 -/
#guard_msgs in #eval 0.1

/- `Float` を関数 `Float.toRat0` で有理数に変換してみると、誤差の存在が明るみになります。-/

-- `1/10` にはならない！
/-- info: (3602879701896397 : Rat)/36028797018963968 -/
#guard_msgs in #eval (0.1 : Float).toRat0

-- 分母の数は2の冪乗になっている
-- これは浮動小数点数が内部で2進数で表現されていることを裏付ける
#eval 2 ^ Nat.log2 36028797018963968 = 36028797018963968

/- これでは誤差の存在はわかってもその大きさが分かりづらいので、10進数として正確な表現を出力してみましょう。 -/

/-- 分母が2のベキであるような正の有理数を10進小数として表示する -/
def Rat.pow2ToBase10Pos (x : Rat) : String :=
  -- 整数部分
  let integerPart := toString x.floor

  -- `x` の分母は `2ⁱ` という形をしていると仮定したので、その指数 `i` を求めておく
  let i := Nat.log2 x.den

  -- 小数部分を`x` の分母が `2ⁱ` であることを利用して計算する
  let decimalPart := (x.num % x.den) * 5 ^ i
    |> toString
    |>.leftpad i '0'

  integerPart ++ "." ++ decimalPart

/-- 分母が2のベキであるような有理数を10進小数として表示する -/
def Rat.pow2ToBase10 (x : Rat) : String :=
  if 0 ≤ x then x.pow2ToBase10Pos else "-" ++ (-x).pow2ToBase10Pos

/-- `Float` を丸めを行わずに正確に表示する -/
def Float.toExactDecimal (x : Float) : String := x.toRat0.pow2ToBase10

/-- info: "0.1000000000000000055511151231257827021181583404541015625" -/
#guard_msgs in #eval Float.toExactDecimal 0.1

-- ２進数で表現されているので、0.5 は正確に表現できる
/-- info: "0.5" -/
#guard_msgs in #eval Float.toExactDecimal 0.5

/- `Float` では明らかに正しそうに見える等式がしばしば誤差のために偽になるということに注意してください。-/

-- 等しそうに見えるが、等しくない
#guard 0.1 + 0.2 != 0.3

-- 両辺を `#eval` で評価してみても理由はわからない…

/-- info: 0.300000 -/
#guard_msgs in #eval 0.1 + 0.2

/-- info: 0.300000 -/
#guard_msgs in #eval 0.3

-- 両辺の正確な値を表示させてみると理由がわかる

-- `0.1 + 0.2 : Float` は `0.3 : Rat` より大きい
/-- info: "0.3000000000000000444089209850062616169452667236328125" -/
#guard_msgs in
  #eval Float.toExactDecimal (0.1 + 0.2)

-- `0.3 : Float` は `0.3 : Rat` より小さい
/-- info: "0.299999999999999988897769753748434595763683319091796875" -/
#guard_msgs in
  #eval Float.toExactDecimal 0.3
