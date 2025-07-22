/-
# 問題 4
(初級 🌟) リストの要素数を求めよ。
-/
variable {α : Type}

def myLength (l : List α) : Nat :=
  match l with
  | [] => 0
  | _ :: a => myLength a + 1

#guard myLength [123, 456, 789] == 3
#guard myLength ['L', 'e', 'a', 'n', '4'] == 5
#guard myLength [False, True, True] == 3
