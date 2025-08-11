/- # Applicative

`Applicative` 型クラスは、[`Functor`](#{root}/TypeClass/Functor.md) 型クラスの拡張であり、[`Monad`](#{root}/TypeClass/Monad.md) 型クラスよりは制限された中間的な構造で、関数適用を一般化したものであると見なすことができます。

## 定義

`Applicative` 型クラスは、大雑把に書けば次のように定義されています。(実際の定義はもっと複雑です)

{{#include ./Applicative/Def.md}}

すなわち、関数 `F : Type → Type` を `Applicative` 型クラスのインスタンスにするということは、`pure : α → F α` と `(· <*> ·) : F (α → β) → F α → F β` を定義するということです。
-/

/-- 標準にある`Option`を真似て構成した関手 -/
inductive MyOption (α : Type) where
  | none
  | some (a : α)

/-- `MyOption`を`Applicative`のインスタンスにする -/
instance : Applicative MyOption where
  pure a := MyOption.some a
  seq f a :=
    match f, a () with
    | .some f, .some a => .some (f a)
    | _, _ => .none

/- ## Functor との違い

`Functor.map` メソッドは `(α → β) → F α → F β` という型を持ちます。これは、`F = Id` の場合を考えてみると分かるように、１引数の関数適用を一般化したものだと考えることができます。では２引数、３引数の時はどうなるでしょうか？

単純に拡張すると、２引数の時は `(α → β → γ) → F α → F β → F γ` という型になり、３引数の時は `(α → β → γ → δ) → F α → F β → F γ → F δ` という型になります。これらを `Functor.map` を使って表現するのは困難です。

しかし、`F` が `Applicative` 型クラスのインスタンスになっていれば、n 引数の場合でも表現することができます。[^PIH]
-/

variable {α β γ δ : Type}
variable {F : Type → Type} [Applicative F]

/-- 1引数の場合 -/
example : (α → β) → F α → F β := fun f x =>
  pure f <*> x

/-- 2引数の場合 -/
example : (α → β → γ) → F α → F β → F γ := fun f x y =>
  pure f <*> x <*> y

/-- 3引数の場合 -/
example : (α → β → γ → δ) → F α → F β → F γ → F δ := fun f x y z =>
  pure f <*> x <*> y <*> z

/-
[^PIH]: ここでの説明は 「プログラミングHaskell 第2版」(Graham Hutton 著、山本和彦訳)を参考にしました。
-/
