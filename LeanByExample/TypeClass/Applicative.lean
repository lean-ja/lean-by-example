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

end Hidden --#
