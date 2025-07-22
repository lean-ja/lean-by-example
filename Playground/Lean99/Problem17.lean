/-
# 問題 17
(初級 🌟) リストを2つの部分に分割せよ。最初の部分の長さは指定される。
-/
variable {α : Type}

-- 以下の関数は使わないこと
#check List.take
#check List.drop

def split (l : List α) (n : Nat) : List α × List α :=
  match l, n with
  | [], _ => ([], [])
  | _, 0 => ([], l)
  | h :: t, n =>
    let (a, b) := split t (n - 1)
    (h :: a, b)

#guard split [1, 2, 3, 4, 5] 2 == ([1, 2], [3, 4, 5])
#guard split ["a"] 3 == (["a"], [])
#guard split ["a", "b", "c", "d", "e", "f"] 3 == (["a", "b", "c"], ["d", "e", "f"])
