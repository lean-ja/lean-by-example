/-
# 問題 1
(初級 🌟) リストの最後の要素を求めよ。
-/
variable {α : Type}

def myLast (l : List α) : Option α :=
  match l with
  | [] => none
  | [a] => a
  | _ :: as => myLast as

#guard myLast [1, 2, 3, 4] == some 4
#guard myLast [1] == some 1
#guard myLast ['x', 'y', 'z'] == some 'z'
