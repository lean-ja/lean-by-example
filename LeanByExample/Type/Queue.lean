/- # Queue

`Std.Queue` は、**FIFO キュー(先入れ先出しキュー)** です。キューとは、「先に追加した要素が先に取り出される」データ構造のことで、たとえばレジ待ちの行列はキューの例になっています。

内部的には 2 本の `List` を持つ構造体として実装されています。
-/
import Std

open Std
--#--
/--
info: structure Std.Queue.{u} (α : Type u) : Type u
number of parameters: 1
fields:
  Std.Queue.eList : List α :=
    []
  Std.Queue.dList : List α :=
    []
constructor:
  Std.Queue.mk.{u} {α : Type u} (eList dList : List α) : Queue α
-/
#guard_msgs in #print Std.Queue
--#--
namespace Hidden --#

structure Queue.{u} (α : Type u) where
  eList : List α := []
  dList : List α := []

end Hidden --#
/-
`dList` は次に取り出す側のリスト、`eList` は追加された要素をスタック的に貯めていくリストです。

キューの中身は `dList ++ eList.reverse` と常に一致します。
-/

/- ## 基本操作

`Queue` の基本操作を紹介します。

### 空のキュー

`empty` で空のキューを作成できるほか、`isEmpty` 関数で空かどうかを判定できます。`empty` のことを `∅` と書くこともできます。
-/

#guard (Queue.empty : Queue Nat).isEmpty

#guard (∅ : Queue Nat).isEmpty

/- ### 要素の追加

`enqueue` でキューの末尾に要素を追加できます。`toArray` で内容を配列として取り出せます。
-/

/-⋆-//-- info: #[10, 20] -/
#guard_msgs in --#
#eval (∅ : Queue Nat)
  |>.enqueue 10
  |>.enqueue 20
  |>.toArray

/- `enqueueAll` で、複数の要素をキューに追加できます。このとき順序が逆になることに注意してください。 -/

#guard
  let q := (∅ : Queue Nat).enqueueAll [10, 20]
  q.toArray = #[20, 10]

/- ### 要素の取り出し

`Queue.dequeue?` でキューの先頭から要素を取り出せます。キューが空の場合は `none` を、空でない場合は「取り出した値」と「残りのキュー」のペアを `some` で包んで返します。
-/

/-- キューから2つの要素を順番に取り出す -/
def popTwo {α : Type} (q : Queue α) : Option (α × α) := do
  let (x, q) ← q.dequeue?
  let (y, _) ← q.dequeue?
  return (x, y)

-- 10 を入れて 20 を入れると、
-- 取り出すときには 10 が出て次に 20 が出てくる
#guard
  let q := ((∅ : Queue Nat).enqueue 10).enqueue 20
  popTwo q = some (10, 20)

-- 空のキューからは取り出せない
#guard (∅ : Queue Nat).dequeue? = none

/-
## 使用例

キューというデータ構造の典型的な応用例として、**幅優先探索 (BFS)** が挙げられます。

以下は `Queue` を使って二分木のノード値を幅優先順で列挙する例です。
-/

/-- 二分木 -/
inductive Tree (α : Type) where
  | leaf : Tree α
  | node (val : α) (left right : Tree α) : Tree α

/-- `Queue` を使って二分木のノード値を幅優先順 (BFS) で列挙する -/
partial def Tree.bfsValues {α : Type} (t : Tree α) : List α :=
  go ((∅ : Queue (Tree α)).enqueue t) []
where
  go (q : Queue (Tree α)) (acc : List α) : List α :=
    match q.dequeue? with
    | none => acc.reverse
    | some (.leaf, q') => go q' acc
    | some (.node v left right, q') =>
      go ((q'.enqueue left).enqueue right) (v :: acc)

/-- テスト用の二分木

```
    1
   / \
  2   3
 / \
4   5
```
-/
def sampleTree : Tree Nat :=
  .node 1 (.node 2 (.node 4 .leaf .leaf) (.node 5 .leaf .leaf)) (.node 3 .leaf .leaf)

-- 幅優先順で列挙すると [1, 2, 3, 4, 5] になる
#guard Tree.bfsValues sampleTree = [1, 2, 3, 4, 5]
