/- # Array

`Array α` は配列を表す型です。特定の型 `α : Type u` の要素を一直線に並べたものです。
`#[a₁, ..., aₖ]` という記法で `Array α` の項を作ることができます。
-/

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
/- しかしドキュメントコメントに以下のように書かれている通り、実行時には `List` とは大きく異なる動的配列(dynamic array)としての振る舞いを見せます。

{{#include ./Array/Doc.md}}

`List` のラッパーとしての定義は、証明を行おうとしたときに参照されます。-/

/- ## 基本的な操作

### インデックスアクセス

配列は [`GetElem`](#{root}/TypeClass/GetElem.md) のインスタンスであり、`i` 番目の要素を取得するために `a[i]` という記法が使用できます。`Array α` は実行時には動的配列として振る舞うので、インデックスアクセスは高速に行うことができます。
-/

#guard #[1, 2, 3][0] = 1

#guard #[1, 2, 3][3]? = none

/- ### 要素の追加

`xs : Array α` に対して `Array.push` 関数で末尾に要素を追加できます。

ドキュメントコメントに次のように書かれている通り、この操作は高速に行うことができます。

{{#include ./Array/PushDoc.md}}
-/

#guard #[1, 2, 3].push 4 = #[1, 2, 3, 4]

/- ## List と比較した特長

[`List`](#{root}/Type/List.md) も同様にインデックスアクセスをサポートしていますが、`Array` の方がより高速にアクセスすることができます。

なぜかというと、`List` は連結リストとして実装されており、`i : Nat` 番目にアクセスしようとすると最初の要素から順に辿っていく必要があるからです。一方で `Array` は動的配列として実装されているので、`i` 番目の要素に直接アクセスできます。

{{#include ./Array/IdxAccess.md}}
-/
