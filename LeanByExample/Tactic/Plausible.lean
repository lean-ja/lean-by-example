/- # plausible

`plausible` は、証明しようとしているゴールが間違っていないかランダムに例を生成してチェックし、反例を見つけるとエラーで警告するタクティクです。 -/
import Plausible

section --#

variable (a b : Nat)
set_option warn.sorry false --#

/-⋆-//-- error: Found a counter-example! -/
#guard_msgs (error) in --#
example (h : 0 ≤ a + b) : 1 ≤ a := by
  plausible (config := { quiet := true })
  sorry

end --#
/-
100 個のテストケースでテストして反例が見つからなかった場合、ギブアップして [`sorry`](./Sorry.md) と同様にはたらきます。
-/
set_option warn.sorry false in --#

/-⋆-//-- warning: Gave up after failing to generate values that fulfill the preconditions 100 times. -/
#guard_msgs (warning) in --#
example (a : Nat) : a ≠ a → a ≤ 1 := by
  plausible

/- 同様の機能を持つコマンドとして [`#test`](#{root}/Diagnostic/Test.md) コマンドがあります。-/

/- ## 引数
引数として、オプションを渡すことができます。

### numInst

`numInst` を設定すると、ギブアップするまでに行うテストの回数を指定することができます。
-/
set_option warn.sorry false in --#

/-⋆-//-- warning: Gave up after failing to generate values that fulfill the preconditions 10 times. -/
#guard_msgs (warning) in --#
example (a : Nat) : a ≠ a → a ≤ 1 := by
  plausible (config := { numInst := 10 })

/- ## カスタマイズ

組み込みではない、自作の型に対して `plausible` は準備なしには使うことができません。
-/

open Plausible

/-- 自前で `Nat` を模倣して定義した型 -/
inductive MyNat where
  | zero
  | succ (n : MyNat)
deriving Repr

set_option warn.sorry false in --#

example : ∀ (a b : MyNat), a = b := by
  -- `plausible` は最初使うことができない
  fail_if_success plausible

  sorry

/- ここで定義した `MyNat` のような自作の型に対して `plausible` を使用するためには、いくつかのステップがあります。 -/

/- ### 1. Shrinkable クラスのインスタンスにする

`plausible` が反例を見つけたときに、「より小さな反例を見つける」ことができるようにするために、`Shrinkable` 型クラスのインスタンスを実装する必要があります。
-/

/-- 引数よりも小さい `MyNat` の項のリストを返す -/
def MyNat.shrink : MyNat → List MyNat
  | zero => []
  | succ n => n :: n.shrink

instance : Shrinkable MyNat where
  shrink := MyNat.shrink

/- ### 2. SampleableExt クラスのインスタンスにする

`plausible` はテストするための要素をランダムに生成します。その方法を指定するのが `SampleableExt` 型クラスです。
-/

/-- 組み込みの自然数を `MyNat` に変換する -/
def MyNat.ofNat : Nat → MyNat
  | 0 => zero
  | n + 1 => succ (ofNat n)

open SampleableExt in

instance : SampleableExt MyNat := mkSelfContained do
  let x ← SampleableExt.interpSample Nat
  return MyNat.ofNat x

/- `SampleableExt` 型クラスのインスタンスであることは、`#sample` コマンドで確認できます。-/

#sample MyNat

/- ### 3. 決定可能にする

`plausible` でテストが行えるようにするためには、テスト対象の主張が決定可能（`Decidable` 型クラスのインスタンス）である必要があります。
-/

-- `MyNat` 同士の比較を決定可能にする
deriving instance DecidableEq for MyNat

/- 以上の準備で `plausible` が使えるようになります。 -/

/-⋆-//-- error: Found a counter-example! -/
#guard_msgs in --#
example : ∀ (a b : MyNat), a = b := by
  -- `plausible` が使えるようになった！
  plausible (config := { quiet := true})
