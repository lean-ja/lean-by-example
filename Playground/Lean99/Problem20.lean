/-
# 問題 20
(初級 🌟) リストからK番目の要素を削除せよ。
-/
variable {α : Type}

def removeAt (l : List α) (n : Nat) : List α :=
  match l, n with
  | [], _ => []
  | _, 0 => l
  | _ :: b, 1 => b
  | x :: b, m + 2 => x :: removeAt b (m + 1)

#guard removeAt ['a', 'b', 'c', 'd'] 2 == ['a', 'c', 'd']
#guard removeAt ['a', 'b', 'c', 'd'] 5 == ['a', 'b', 'c', 'd']
#guard removeAt ['a', 'b', 'c', 'd'] 0 == ['a', 'b', 'c', 'd']
#guard removeAt ['a'] 1 == []
