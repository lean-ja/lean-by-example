/- # Functor

`Functor` は圏論における関手(functor)という概念からその名がある型クラスで、非常に雑な表現をすると、この型クラスを実装した型は「値を包んでいる」ものとして扱うことができます。

より詳細には、`f : Type u → Type v` に対して `Functor` はおおむね次のように定義されています。(実際の定義とは異なります)
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
