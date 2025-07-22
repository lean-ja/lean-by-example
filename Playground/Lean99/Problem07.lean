/-
# 問題 7
(中級 🌟🌟) ネストしたリスト構造を平坦化せよ（1次元リストにせよ）。
-/

variable {α : Type}

-- Leanのリストは同種要素のみなので、新しいデータ型を定義する必要がある
inductive NestedList (α : Type) where
  | elem : α → NestedList α
  | list : List (NestedList α) → NestedList α

/-- NestedList を String に変換する -/
partial def NestedList.toString [ToString α] : NestedList α → String
  | NestedList.elem x => ToString.toString x
  | NestedList.list xs => "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

/-- `#eval` で NestedList を見やすく表示する -/
instance [ToString α] : ToString (NestedList (α : Type)) where
  toString nl := NestedList.toString nl

/-- ネストしたリスト構造を平坦化する -/
def flatten (nl : NestedList α) : List α :=
  match nl with
  | .elem x => [x]
  | .list [] => []
  | .list (x :: xs) => flatten x ++ flatten (.list xs)

open NestedList

def sample : NestedList Nat :=
  list [elem 1, list [elem 2, elem 3], elem 4]

#eval sample

def empty : NestedList String := list []

#eval empty

#guard flatten (.elem 5) == [5]
#guard flatten sample == [1, 2, 3, 4]
#guard flatten (empty) == []
