/-
# 問題 21
(初級 🌟) 指定した位置に要素を挿入せよ。
-/
variable {α : Type}

def insertAt (e : α) (l : List α) (i : Nat) : List α :=
  match l, i with
  | a :: b , i + 2 => a :: insertAt e b (i + 1)
  | _ , _ => e :: l

#guard insertAt "X" ["1", "2", "3", "4"] 2 == ["1", "X", "2", "3", "4"]
#guard insertAt "X" ["1", "2", "3", "4"] 1 == ["X", "1", "2", "3", "4"]
#guard insertAt "X" [] 1 == ["X"]
