/- # Queue

`Std.Queue` は、永続的・関数型の **FIFO キュー(先入れ先出しキュー)** です。キューとは、「最初に追加した要素が最初に取り出される」データ構造です。

「永続的」というのは、`enqueue` や `dequeue?` が元のキューを破壊的に変更せず、新しいキューを返すという意味です。

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
`dList` は次に取り出す側のリスト、`eList` は追加された要素を逆順に溜める側のリストです。キューの中身は `dList ++ eList.reverse` で表されます。
-/

/- ## 基本操作

`Queue` の基本操作を紹介します。

### 空のキュー

`∅` で空のキューを作成できます。`isEmpty` 関数で空かどうかを判定できます。
-/

/-⋆-//-- info: true -/
#guard_msgs in --#
#eval (∅ : Queue Nat).isEmpty

/- ### enqueue: 要素の追加

`Queue.enqueue` でキューの末尾に要素を追加できます。`toArray` で内容を配列として取り出せます。
-/

/-⋆-//-- info: #[10, 20] -/
#guard_msgs in --#
#eval ((∅ : Queue Nat).enqueue 10).enqueue 20 |>.toArray

/- `enqueue` は元のキューを変更せず、新しいキューを返します。 -/

def emptyQueue : Queue Nat := ∅

def oneElementQueue : Queue Nat := emptyQueue.enqueue 10

#guard emptyQueue.isEmpty
#guard oneElementQueue.toArray = #[10]

/-
```admonish warning title="enqueue の引数順"
`Queue.enqueue` は第1引数に追加する値、第2引数にキューを取ります。そのため、`q.enqueue 10` というドット記法は、実際には `Queue.enqueue 10 q` という呼び出しになります。これは `q` に `10` を末尾追加する操作です。
```
-/

/-⋆-//-- info: Std.Queue.enqueue.{u} {α : Type u} (v : α) (q : Queue α) : Queue α -/
#guard_msgs in --#
#check Queue.enqueue

-- ドット記法ではキューが第2引数の位置に渡される
example (q : Queue Nat) : q.enqueue 10 = Queue.enqueue 10 q := by
  rfl

/- ### dequeue?: 要素の取り出し

`Queue.dequeue?` でキューの先頭から要素を取り出せます。キューが空の場合は `none` を、空でない場合は「取り出した値」と「残りのキュー」のペアを `some` で返します。

`do` 記法と組み合わせると、複数の要素を順番に取り出すことができます。
-/

/-- キューから2つの要素を順番に取り出す -/
def popTwo : Option (Nat × Nat) := do
  let q := ((∅ : Queue Nat).enqueue 10).enqueue 20
  let (x, q) ← q.dequeue?
  let (y, _) ← q.dequeue?
  return (x, y)

/-⋆-//-- info: some (10, 20) -/
#guard_msgs in --#
#eval popTwo

-- 空のキューからは取り出せない
#guard (∅ : Queue Nat).dequeue? = none

-- 取り出したあとのキューには、次に取り出される要素が残っている
#guard
  let q := ((∅ : Queue Nat).enqueue 10).enqueue 20
  match q.dequeue? with
  | none => false
  | some (x, q') => x = 10 && q'.toArray == #[20]

/- ## 計算量

`Queue` の各操作の計算量は次のとおりです。

* `enqueue` : O(1)
* `dequeue?` : 償却 O(1)、最悪 O(n)

`dequeue?` の計算量が最悪 O(n) になるのは、`dList` が空になったとき内部で `eList.reverse` が実行されるためです。ただし、いったん反転した要素はその後しばらく O(1) で取り出せるため、一連の操作全体では償却 O(1) になります。

## 使用例

`Queue` は「取り出す順序を保ちたいが、純粋関数型で効率的に動作させたい」場面に適しています。典型的な応用例として、**幅優先探索 (BFS)** が挙げられます。

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

/- 以下の二分木でテストします。

```
    1
   / \
  2   3
 / \
4   5
```
-/

-- テスト用の二分木
def sampleTree : Tree Nat :=
  .node 1 (.node 2 (.node 4 .leaf .leaf) (.node 5 .leaf .leaf)) (.node 3 .leaf .leaf)

-- 幅優先順で列挙すると [1, 2, 3, 4, 5] になる
#guard Tree.bfsValues sampleTree = [1, 2, 3, 4, 5]
