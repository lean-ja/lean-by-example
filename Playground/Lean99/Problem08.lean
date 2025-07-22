/-
# 問題 8
(中級 🌟🌟) リストの連続する重複要素を削除せよ。
-/
variable {α : Type} [BEq α]

def compress (l : List α) : List α :=
  match l with
  | [] => []
  | a :: b => a :: comp' b a
where
  comp' (ls : List α) (x : α) : List α :=
    match ls with
    | [] => []
    | a' :: l' =>
      if a' == x then
        comp' l' a'
      else
        a' :: comp' l' a'

#guard compress [1, 1, 2, 2, 1, 2, 2] == [1, 2, 1, 2]
#guard compress ['C', 'o', 'o', 'o', 'p', 'y', 'y'] == ['C', 'o', 'p', 'y']
