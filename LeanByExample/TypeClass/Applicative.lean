/- # Applicative

`Applicative` 型クラスは、[`Functor`](#{root}/TypeClass/Functor.md) 型クラスの拡張であり、[`Monad`](#{root}/TypeClass/Monad.md) 型クラスよりは制限された中間的な構造で、関数適用を任意の計算効果に対して一般化したものであると見なすことができます。

## 定義

`Applicative` 型クラスは、大雑把に書けば次のように定義されています。(実際の定義はもっと複雑です)

{{#include ./Applicative/Def.md}}
-/
