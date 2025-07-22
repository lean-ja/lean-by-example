/-
# 問題 26
(中級 🌟🌟) リストのN個の要素からK個の異なる要素の組み合わせをすべて生成せよ。
-/
variable {α : Type}

def List.combinations (k : Nat) (l : List α) : List (List α) :=
  match k, l with
  | 0, _ => [[]]
  | _, [] => []
  | k + 1, x :: xs =>
    ((x :: ·) <$> (List.combinations k xs)) ++ (List.combinations (k + 1) xs)

#guard [1, 2, 3, 4].combinations 2 == [[1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4]]
#guard [1, 2, 3, 4].combinations 3 == [[1, 2, 3], [1, 2, 4], [1, 3, 4], [2, 3, 4]]
#guard ['a', 'b', 'c'].combinations 1 == [['a'], ['b'], ['c']]
