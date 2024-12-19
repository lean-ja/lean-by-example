/- # Array

`Array α` は配列を表す型です。特定の型 `α : Type u` の要素を一直線に並べたものです。
`#[a₁, ..., aₖ]` という記法で `Array α` の項を作ることができます。
-/
import Lean --#

#check (#[1, 2, 3] : Array Nat)

#check (#["hello", "world"] : Array String)

/- ## 定義と実行時の性質

`Array α` は次のように連結リスト `List α` のラッパーとして定義されているように見えます。-/
--#--
/--
info: structure Array.{u} (α : Type u) : Type u
number of parameters: 1
fields:
  Array.toList : List α
constructor:
  Array.mk.{u} {α : Type u} (toList : List α) : Array α
-/
#guard_msgs in #print Array
--#--

namespace Hidden --#

structure Array.{u} (α : Type u) : Type u where
  toList : List α

end Hidden --#
/- しかしドキュメントコメントに以下のように書かれている通り、実行時には `List` とは大きく異なる動的配列(dynamic array)としての振る舞いを見せます。-/

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name ← liftCoreM do realizeGlobalConstNoOverload x
  if let some s ← findDocString? (← getEnv) name then
  logInfo m!"{s}"

/--
info: `Array α` is the type of [dynamic arrays](https://en.wikipedia.org/wiki/Dynamic_array)
with elements from `α`. This type has special support in the runtime.

An array has a size and a capacity; the size is `Array.size` but the capacity
is not observable from Lean code. Arrays perform best when unshared; as long
as they are used "linearly" all updates will be performed destructively on the
array, so it has comparable performance to mutable arrays in imperative
programming languages.

From the point of view of proofs `Array α` is just a wrapper around `List α`.
-/
#guard_msgs in #doc Array

/- `List` のラッパーとしての定義は、証明を行おうとしたときに参照されます。-/

/- ## インデックスアクセス

配列は [`GetElem`](#{root}/Reference/TypeClass/GetElem.md) のインスタンスであり、`i` 番目の要素を取得するために `a[i]` という記法が使用できます。
-/

#guard #[1, 2, 3][0] = 1

#guard #[1, 2, 3][3]? = none

/- ## 要素の追加

`xs : Array α` に対して `Array.push` 関数で末尾に要素を追加できます。
-/

#guard #[1, 2, 3].push 4 = #[1, 2, 3, 4]
