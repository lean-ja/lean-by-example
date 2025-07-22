/-
# 問題 16
(中級 🌟🌟) リストからN番目ごとの要素を削除せよ。
-/
variable {α : Type}

def dropEvery (l : List α) (n : Nat) : List α :=
  helper l n 1
where
  helper : List α → Nat → Nat → List α
  | [], _, _ => []
  | x :: xs, n, m =>
    if m % n = 0 then
      helper xs n (m + 1)
    else
      x :: helper xs n (m + 1)

#guard dropEvery [1, 2, 3] 0 == [1, 2, 3]
#guard dropEvery ['a', 'b', 'c', 'd'] 2 == ['a', 'c']
#guard dropEvery ['a', 'b', '3', 'c', 'd', '6', 'e'] 3 == ['a', 'b', 'c', 'd', 'e']
