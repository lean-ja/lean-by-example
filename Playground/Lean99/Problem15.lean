/-
# 問題 15
(中級 🌟🌟) リストの各要素を指定回数だけ複製せよ。
-/

variable {α : Type}

def repli (l : List α) (n : Nat) : List α :=
  match l with
  | [] => []
  | a :: b => (solorepl a n) ++ repli b n
where
  solorepl (x : α) (n : Nat) : List α :=
    match n with
    | 0 => []
    | m + 1 => x :: solorepl x m

#guard repli [1, 2, 3] 3 == [1, 1, 1, 2, 2, 2, 3, 3, 3]
#guard repli [1, 2, 3] 2 == [1, 1, 2, 2, 3, 3]
#guard repli [1, 2, 3] 1 == [1, 2, 3]
#guard repli [1, 2, 3] 0 == []
