/-
# 問題 14
(初級 🌟) リストの各要素を2回ずつ複製せよ。
-/

variable {α : Type}

def dupli (l : List α) : List α :=
  match l with
  | [] => []
  | a :: b => a :: a :: dupli b

#guard dupli [1, 2, 3] == [1, 1, 2, 2, 3, 3]
#guard dupli ['a', 'b', 'c', 'c', 'd'] == ['a', 'a', 'b', 'b', 'c', 'c', 'c', 'c', 'd', 'd']
