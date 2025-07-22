/-
# 問題 5
(初級 🌟) リストを逆順にせよ。
-/
variable {α : Type}

def myReverse (l : List α) : List α :=
  match l with
  | [] => []
  | a :: as => myReverse as ++ [a]

#guard myReverse [1, 2, 3, 4] == [4, 3, 2, 1]
#guard myReverse ["man", "plan", "canal", "panama"] == ["panama", "canal", "plan", "man"]
