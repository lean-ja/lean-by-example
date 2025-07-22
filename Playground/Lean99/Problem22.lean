/-
# 問題 22
(初級 🌟) 指定した範囲の整数をすべて含むリストを作成せよ。
-/

def range (m n : Int) : List Int :=
  generate m (n - m + 1).toNat
where
  generate (start : Int) (length : Nat) : List Int :=
    match length with
    | 0 => []
    | l + 1 => generate start l ++ [start + l]

#guard range 4 9 == [4, 5, 6, 7, 8, 9]
#guard range (-1) 2 == [-1, 0, 1, 2]
#guard range (-2) (-1) == [-2, -1]
