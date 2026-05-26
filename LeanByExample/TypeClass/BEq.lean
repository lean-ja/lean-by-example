/- # BEq

`BEq` は、`==` と `!=` による `Bool` 値の比較を提供する型クラスです。
たとえば `Nat` には `BEq` のインスタンスがあるので、2つの自然数を `==` で比較することができます。
-/

#check (BEq : Type → Type)

#check ((· == ·) : Nat → Nat → Bool)

#guard ((2 : Nat) == 2)
#guard !((2 : Nat) == 3)

#guard ((2 : Nat) != 3)

/- ## 定義

`BEq` 型クラスは、比較関数 `beq : α → α → Bool` を持ちます。
`a == b` という記法は、この `beq a b` を使います。
-/

namespace Hidden --#

class BEq.{u} (α : Type u) where
  /-- `α` 型の2つの値が等しいとみなせるかどうかを `Bool` 値で返す。 -/
  beq : α → α → Bool

end Hidden --#

/- ## インスタンスを定義する

自分で定義した型に対して `BEq` インスタンスを定義すると、その型の値を `==` で比較できるようになります。

次の例では、アカウントを `id` だけで比較することにします。
-/

structure Account where
  id : Nat
  name : String
  deriving DecidableEq, Repr

instance : BEq Account where
  beq a b := a.id == b.id

def alice : Account := { id := 1, name := "Alice" }

def alicia : Account := { id := 1, name := "Alicia" }

def bob : Account := { id := 2, name := "Bob" }

-- id が同じなので `BEq` では等しい
#guard (alice == alicia)

-- id が異なるので `BEq` では等しくない
#guard !(alice == bob)

-- しかし命題としての等号では等しくない
example : alice ≠ alicia := by decide

/- ## DecidableEq との違い

[`DecidableEq`](#{root}/TypeClass/Decidable.md) は、`a = b` という命題が決定可能であることを表します。
一方で `BEq` は、`a == b` という `Bool` 値の比較を提供するだけです。

したがって `BEq` は、それだけでは `==` が反射的であることも、命題としての等号 `=` と一致することも要求しません。
上の `Account` の例では、`alice == alicia` は `true` ですが、`alice = alicia` は成り立ちません。
-/

#check (DecidableEq : Type → Type)

/- ## LawfulBEq

`==` と `=` が一致することを使いたいときは、`LawfulBEq` が必要です。
上の `Account` の `BEq` は `alice == alicia` が真なのに `alice ≠ alicia` なので、`LawfulBEq` ではありません。
-/

/-⋆-//--
error: failed to synthesize
  LawfulBEq Account

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in --#
#synth LawfulBEq Account

/- 構造体のすべてのフィールドを比較する通常の等号でよければ、`BEq` と `LawfulBEq` は `deriving` できます。-/

structure Point where
  x : Nat
  y : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

#synth BEq Point

#synth LawfulBEq Point

#guard ({ x := 2, y := 3 } : Point) == { x := 2, y := 3 }

example : ({ x := 2, y := 3 } : Point) = { x := 2, y := 3 } := by decide

/- ## Float の例

`Float` は `DecidableEq` と `BEq` の違いが重要になる例です。
Lean の `Float` は IEEE 754 の浮動小数点数に対応しており、公式リファレンスでは、浮動小数点数の等号は Lean の論理内では決定可能ではないと説明されています。

参照:
* [Boolean Equality Tests](https://lean-lang.org/doc/reference/latest/Type-Classes/Basic-Classes/#boolean-equality-tests)
* [Floating-Point Numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/)
-/

#check (inferInstance : BEq Float)

/-⋆-//--
error: failed to synthesize
  DecidableEq Float

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in --#
#synth DecidableEq Float

/- しかし `Float` には実行時の比較としての `BEq` はあります。たとえば `0.0 / 0.0` は `NaN` になり、IEEE 754 の比較では `NaN` は自分自身と比較しても等しくありません。-/

#guard ((0.0 : Float) / 0.0).isNaN

-- 自分自身と比較しても false になる
#guard !(((0.0 : Float) / 0.0) == ((0.0 : Float) / 0.0))

-- 通常の数値の比較は true になる
#guard ((1.0 : Float) == 1.0)
