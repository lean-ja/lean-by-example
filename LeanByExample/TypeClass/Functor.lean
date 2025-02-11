/- # Functor

`Functor` は圏論における **関手(functor)** という概念からその名がある型クラスで、非常に雑な表現をすると、この型クラスを実装した型は「値を包んでいるコンテナのようなもの」として扱うことができます。特定のデータ構造に「包まれて」いる中の値に対して関数を適用していくという操作を行いたいことがありますが、`Functor` のインスタンスはそれを可能にします。

より詳細には、`F : Type u → Type v` に対して `Functor` はおおむね次のように定義されています。
-/
namespace Hidden --#
--#--
/--
info: class Functor.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
number of parameters: 1
fields:
  Functor.map : {α β : Type u} → (α → β) → f α → f β
  Functor.mapConst : {α β : Type u} → α → f β → f α
constructor:
  Functor.mk.{u, v} {f : Type u → Type v} (map : {α β : Type u} → (α → β) → f α → f β)
    (mapConst : {α β : Type u} → α → f β → f α) : Functor f
-/
#guard_msgs in #print Functor
--#--

universe u v

/-- 関手 -/
class Functor (F : Type u → Type v) : Type (max (u+1) v) where
  /-- 関数 `f : α → β` を関数 `F α → F β` に変換する -/
  map : {α β : Type u} → (α → β) → F α → F β

  /-- `a : α` に対して、定数関数 `const a : β → α` を関数 `F β → F α` に変換する。
  `map` を使うよりも効率的に実装できることがあるので、上書きできるように用意されている。-/
  mapConst : {α β : Type u} → α → F β → F α := Function.comp map (Function.const _)

end Hidden --#
/- つまり、`Functor` のインスタンスは `map` メソッドが使用できます。これは型からわかるように、関数を関数に写す高階関数で、「普通の関数 `f : α → β`」を「`F` に包まれた関数 `F α → F β`」に持ち上げます。`Functor.map` はよく使われる操作であるため、`<$>` という専用の記法が用意されています。 -/
section --#

-- `F` は Functor であると仮定
variable (F : Type → Type) [Functor F]

-- 関数 `g : α → β` と `x : F α` が与えられたとする
variable {α β : Type} (g : α → β)

-- 高階関数を返す
#check (Functor.map g : F α → F β)

-- `<$>` は `map` と同じ
example (x : F α) : g <$> x = Functor.map g x := rfl

end --#
/- ## 典型的なインスタンス

### List
`Functor` 型クラスの典型的なインスタンスのひとつが [`List`](#{root}/Type/List.md) です。これにより「リストの各要素に関数を適用する」ための簡単な方法が提供されます。
-/

-- リストの各要素を２倍する
#guard (fun x => x * 2) <$> [1, 2, 3, 4, 5] = [2, 4, 6, 8, 10]

/- ### Option
[`Option`](#{root}/Type/Option.md) も `Functor` 型クラスのインスタンスになっています。これにより「`x? : Option` が `some x` の場合に関数を適用し、`none` なら `none` を返す」という操作のための簡単な方法が提供されます。
-/

#guard (fun x => x * 2) <$> some 2 = some 4
#guard (fun x => x * 2) <$> (none : Option Nat) = none

/- ### Id
`Id : Type u → Type u` は「何もしない」関手です。
-/

-- Id は何もしない。ただ単に関数を適用するだけ
/-⋆-//-- info: 20 -/
#guard_msgs in --#
#eval (· * 2) <$> (10 : Id Nat)

/- ### (A → ·)
任意の型 `A : Type u` に対して、`fun X => (A → X)` という対応は関手になります。
-/
section
  universe u v

  /-- 型から、その型への関数型を返す -/
  abbrev Hom (A : Type u) (X : Type v) := A → X

  /-- 関数合成を map として `Hom A` は関手になる -/
  instance {A : Type u} : Functor (Hom A) where
    map f g := f ∘ g

end
/- 上記で定義した `Hom` は Lean の標準ライブラリでは `ReaderM` と呼ばれます。 -/
section

  universe u

  /-- 上で定義した Hom は ReaderM に等しい -/
  example (A : Type u) : ReaderM A = Hom A := rfl

end
/- ## Functor 則

`Functor` 型クラスのインスタンスには満たすべきルールがあります。このルールを破っていても `Functor` 型クラスのインスタンスにすることは可能ですが、避けるべきです。`Functor` 型クラスがルールを満たしていることを証明するためには、[`LawfulFunctor`](#{root}/TypeClass/LawfulFunctor.md) 型クラスを使います。
-/
