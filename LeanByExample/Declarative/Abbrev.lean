/-
# abbrev
`abbrev` は、略称(abbreviation)を宣言するコマンドです。

たとえば、`Nat` 型に別の名前を与えたかったとしましょう。Lean では型も他の項と同様に宣言できるので、次のように書いて問題がないように見えます。
-/
namespace Abbrev0 --#

def NaturalNumber : Type := Nat

/- しかし、ここで定義した `Nat` の別名を項に対して使用するとエラーになります。エラーメッセージには以下の通り「`NaturalNumber` の [`OfNat`](#{root}/TypeClass/OfNat.md) インスタンスが見つかりません」という旨のことが書かれています。これは、Lean が `NaturalNumber` を定義に展開してそれが実は `Nat` に等しいことを知るよりも先に、`42 : NaturalNumber` という表記が定義されているか [`OfNat`](#{root}/TypeClass/OfNat.md) のインスタンスを探そうとしてエラーになったことを示唆します。-/

/-⋆-//--
error: failed to synthesize
  OfNat NaturalNumber 42
numerals are polymorphic in Lean, but the numeral `42` cannot be used in a context where the expected type is
  NaturalNumber
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in --#
#check (42 : NaturalNumber)

end Abbrev0 --#
/- ここでエラーを修正する方法の一つが、`def` の代わりに `abbrev` を使用することです。-/
namespace Abbrev1 --#

abbrev NaturalNumber : Type := Nat

#check (42 : NaturalNumber)

end Abbrev1 --#
/- ## 舞台裏
`abbrev` コマンドを使用すると、裏で `[reducible]` 属性が付与されます。-/

abbrev NaturalNumber : Type := Nat

-- `[reducible]` 属性が付与されている
/-⋆-//--
info: @[reducible] def NaturalNumber : Type :=
Nat
-/
#guard_msgs in --#
#print NaturalNumber
