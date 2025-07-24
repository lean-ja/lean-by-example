/- # HashSet

`Std.HashSet` は、「重複のない集まり」を表すデータ構造です。

`insert` 関数で要素を挿入することができますが、同じ要素を複数回挿入しても１つしか保持されません。
-/
import Lean

open Std

/-⋆-//-- info: Std.HashSet.ofList [1] -/
#guard_msgs in --#
#eval show (HashSet Nat) from Id.run do
  -- 空の `HashSet` を作成
  let mut s : HashSet Nat := {}
  -- `1` を２回挿入
  s := s.insert 1
  s := s.insert 1
  s

/- ## 特長

基本的なコレクション型である [`List`](#{root}/Type/List.md) と比較すると、`HashSet` には以下のような特長があります。

### 要素が存在するか判定するのが高速

`s : HashSet α` にある要素 `a : α` が存在するか判定するのは `List` に比べて高速に行うことができます。

`List` では要素を順にたどって調べる必要があるのでサイズに対して線形時間かかってしまいますが、`HashSet` は（平均的に）定数時間で判定することができます。以下は、実験でそれを確かめたコードです。

{{#include ./HashSet/Contain.md}}
-/
