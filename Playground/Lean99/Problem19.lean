/-
# 問題 19
(中級 🌟🌟) リストをN個左に回転せよ。
-/
variable {α : Type}

def rotate (l : List α) (n : Nat) : List α :=
  let n := n % l.length
  l.drop n ++ l.take n

#guard rotate [1, 2, 3, 4, 5] 2 == [3, 4, 5, 1, 2]
#guard rotate [1, 2, 3] 0 == [1, 2, 3]
#guard rotate [1, 2, 3] 3 == [1, 2, 3]
#guard rotate [1, 2, 3] 1 == [2, 3, 1]
