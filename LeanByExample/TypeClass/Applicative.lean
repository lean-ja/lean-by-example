/- # Applicative

`Applicative` 型クラスは、[`Functor`](#{root}/TypeClass/Functor.md) 型クラスの拡張であり、[`Monad`](#{root}/TypeClass/Monad.md) 型クラスよりは制限された中間的な構造で、関数適用を任意の計算効果に対して一般化したものであると見なすことができます。

## 定義

`Applicative` 型クラスは、大雑把に書けば次のように定義されています。

-/
namespace Hidden --#

/-- `pure` 関数を使えるようにするクラス。
通常、`Monad` または `Applicative` インスタンスを介して利用される。
-/
class Pure.{u, v} (f : Type u → Type v) where
  /--
  `a : α` が与えられたとき、`pure a : f α` は「何もせずに `a` を返すアクション」を表す。

  例:
  * `(pure "hello" : Option String) = some "hello"`
  * `(pure "hello" : Except (Array String) String) = Except.ok "hello"`
  * `(pure "hello" : StateM Nat String).run 105 = ("hello", 105)`
  -/
  pure {α : Type u} : α → f α

/--
`Functor` クラスの `<$>` が通常の関数をファンクタに包まれた値に適用できるのに対し、`<*>` はファンクタの「内部」にある関数を適用する。`f` を副作用を伴う計算として捉えると、`seq` は評価順序を保証し、関数を生成する副作用が引数の値を生成する副作用より先に実行されるようにする。

ほとんどの用途では、`Seq` 自体ではなく `Applicative` あるいは `Monad` を使用すべき。
-/
class Seq.{u, v} (f : Type u → Type v) : Type (max (u+1) v) where
  /--
  `<*>` 演算子の実装。
  モナドにおいては、`mf <*> mx` は `do let f ← mf; x ← mx; pure (f x)` と同じになる。
  つまり、まず関数を評価し、次に引数を評価して適用する。
  予期しない順序で評価されることを避けるために、`mx` は `Unit → f α` という関数を使って遅延的に取得される。
  -/
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

end Hidden --#
