/-
# 問題 3
(初級 🌟) リストのK番目の要素を求めよ。
-/
variable {α : Type}

def elementAt (l : List α) (k : Nat) : Option α :=
  match l, k with
  | [], _ => none
  | _, 0 => none
  | a :: _, 1 => a
  | _ :: a, k + 1 => elementAt a k

#guard elementAt ['a', 'b', 'c', 'd', 'e'] 3 == some 'c'
#guard elementAt ['a', 'b', 'c', 'd', 'e'] 6 == none
#guard elementAt ['a', 'b', 'c', 'd', 'e'] 0 == none
#guard elementAt [1, 2, 3] 2 == some 2
