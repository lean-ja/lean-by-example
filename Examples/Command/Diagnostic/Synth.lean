/- # \#synth
型クラス `C` と型 `T` があるとき、`#synth C T` は `T` が `C` のインスタンスになっているかチェックします。もしインスタンスでなかった場合にはエラーになります。

## 型クラスとは
型クラスとは、複数の型に対して共通の機能や実装を提供するものです。具体例を見てみましょう。たとえば逆数は、複数の型に対して定義されています。
-/
import Mathlib.Data.Rat.Defs -- 有理数 --#
import Mathlib.Data.Real.Basic -- 実数 --#

-- `⁻¹` で逆数を表すことができる
#check (1 : ℚ)⁻¹

-- 実数として見ても同じ
#check (1 : ℝ)⁻¹

/-! 逆数をとる関数 `fun x => x⁻¹` の定義域はどうなっているのでしょうか？定義域を一般の型 `α` に拡張してみて、どうなるか見てみましょう。-/

variable (α : Type)

/--
error: failed to synthesize
  Inv α
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #check (_ : α)⁻¹

/-! 一般の型に対して逆数は定義できないので、エラーになってしまいました。エラーメッセージで `α` は `Inv` のインスタンスではないと言われています。この `Inv` が型クラスです。`Inv` のインスタンスであるような型 `T` に対しては、逆数関数 `(·)⁻¹ : T → T` が定義できるというわけです。-/

/-! ## インスタンスとは
例えば実数 `ℝ` に対して逆数は定義できるだろうと予想されますが、実際 `ℝ` は `Inv` のインスタンスであることが確認できます。
-/

/-- info: Real.instInv -/
#guard_msgs in #synth Inv Real

/-! 自然数 `ℕ` に対しては逆数が定義されていないと予想されますが、実際 `Inv` のインスタンスになっていません。-/

-- エラーになってしまう
#guard_msgs (drop error) in #synth Inv Nat

-- 実際、Inv のインスタンスになっていない
#check_failure (inferInstance : Inv Nat)

/-! 自分で無理やり `ℕ` を `Inv` のインスタンスにしてみると、通るようになります。ここでは逆数関数を常に `1` になる定数関数としてみましょう。-/

instance : Inv Nat := ⟨fun _ => 1⟩

#synth Inv Nat

example : (1 : ℕ)⁻¹ = 1 := by rfl
