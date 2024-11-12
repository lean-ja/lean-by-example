/- # Functor

`Functor` は圏論における関手(functor)という概念からその名がある型クラスで、非常に雑な表現をすると、この型クラスを実装した型は「値を包んでいる」ものとして扱うことができます。

より詳細には、`f : Type u → Type v` に対して `Functor` はおおむね次のように定義されています。(実際の定義には `mapConst` というフィールドがありますが、ここでは省略しました)
-/
namespace Hidden --#
--#--
/--
info: class Functor.{u, v} : (Type u → Type v) → Type (max (u + 1) v)
number of parameters: 1
constructor:
Functor.mk : {f : Type u → Type v} →
  ({α β : Type u} → (α → β) → f α → f β) → ({α β : Type u} → α → f β → f α) → Functor f
fields:
map : {α β : Type u} → (α → β) → f α → f β
mapConst : {α β : Type u} → α → f β → f α
-/
#guard_msgs in #print Functor
--#--

universe u v

/-- 関手 -/
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  /-- 関数 `g : α → β` を `g* : f α → f β` に変換する -/
  map : {α β : Type u} → (α → β) → f α → f β

end Hidden --#
/- つまり、`Functor` のインスタンスは `map` メソッドが使用できます。これは型からわかるように、関数を関数に写す高階関数で、「`f` で包まれる前の関数」から「`f` で包まれた関数」を返します。 -/

-- `f` は Functor であると仮定
variable (f : Type → Type) [Functor f]

-- 関数 `g : α → β` と `x : f α` が与えられたとする
variable {α β : Type} (g : α → β)

-- 高階関数を返す
#check (Functor.map (f := f) g : f α → f β)

/- `Functor.map` はよく使われる操作であるため、`<$>` という専用の記法が用意されています。-/

example (x : f α) : Functor.map g x = g <$> x := rfl

/- ## 典型的なインスタンス

### List
`Functor` 型クラスのインスタンスの典型的な例のひとつが `List` です。
これにより「リストの各要素に関数を適用する」ための簡単な方法が提供されます。
-/

#guard [1, 2, 3, 4, 5].map (fun x => x * 2) = [2, 4, 6, 8, 10]

/- ### Option
`Option` も `Functor` 型クラスのインスタンスになっています。
これにより「`x? : Option` が `some x` の場合に関数を適用し、`none` なら `none` を返す」という操作のための簡単な方法が提供されます。
-/

#guard (some 2).map (fun x => x * 2) = some 4
#guard (none : Option Nat).map (fun x => x * 2) = none

/- ## Functor 則

`Functor` 型クラスのインスタンスには満たすべきルールがあります。
このルールを破っていても `Functor` 型クラスのインスタンスにすることは可能ですが、API の使用者が予期せぬ挙動をするので避けるべきです。
ルール込みで `Functor` 型クラスのインスタンスを定義するためには、[`LawfulFunctor`](./LawfulFunctor.md) 型クラスを使います。
-/

#check LawfulFunctor
