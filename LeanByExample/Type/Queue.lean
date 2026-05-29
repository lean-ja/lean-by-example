/- # Queue

`Std.Queue` は、**FIFO キュー(先入れ先出しキュー)** です。キューとは、「先に追加した要素が先に取り出される」データ構造のことで、たとえばレジ待ちの行列はキューの例になっています。
-/
import Std

open Std

#check Queue
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
## 内部実装

内部的には `Std.Queue` は２本の `List` を持つ構造体として実装されています。
-/
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
`Std.Queue` の２つのフィールドのそれぞれについて説明します。`eList` は追加された要素を貯めていくリストで、キューに追加された要素は `eList` の先頭に追加されます。
-/

/-⋆-//-- info: { eList := [6, 5, 4, 3], dList := [1, 2] } -/
#guard_msgs in --#
#eval
  let q : Queue Nat := { eList := [5, 4, 3], dList := [1, 2] }
  q.enqueue 6

/- `dList` は次に取り出す側のリストです。キューから要素を取り出すとき、まず `dList` の先頭から要素が取り出されます。 -/

/-⋆-//-- info: { eList := [5, 4, 3], dList := [2] } -/
#guard_msgs in --#
#eval
  let q : Queue Nat := { eList := [5, 4, 3], dList := [1, 2] }
  let (_, q') := q.dequeue?.get!
  q'

/- キューの `toArray` による出力は `(dList ++ eList.reverse).toArray` と常に一致します。 -/

example {α : Type} (q : Queue α)
    : (q.dList ++ q.eList.reverse).toArray = q.toArray := by
  simp [Queue.toArray, List.append_toArray, List.reverse_toArray]

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
def Tree.bfsValues {α : Type} (t : Tree α) : Array α := Id.run do
  -- キューを空の状態で初期化
  -- このキューは「これから訪問するべきノード」を管理する
  let mut q : Queue (Tree α) := ∅
  let mut result : Array α := #[]

  -- ルートノードをキューに追加
  q := q.enqueue t

  -- キューが空になるまでループ
  while !q.isEmpty do
    let some (v, q') ← q.dequeue?
      | unreachable!

    match v with
    | .leaf =>
      -- 何も追加せずに次のループへ
      q := q'
      continue
    | .node val left right =>
      result := result.push val

      -- 左の木、右の木の順にキューに追加
      q := q'.enqueue left |>.enqueue right

  return result

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
#guard Tree.bfsValues sampleTree = #[1, 2, 3, 4, 5]
