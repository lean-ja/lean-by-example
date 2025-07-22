/-
# 問題 6
(初級 🌟) リストが回文かどうかを判定せよ。

ヒント: 回文とは前から読んでも後ろから読んでも同じになるリストである（例: (x a m a x)）。
-/
variable {α : Type}

-- `α` の要素同士が等しいかどうか比較できると仮定する
variable [BEq α]

def isPalindrome (l : List α) : Bool :=
  l == l.reverse

#guard isPalindrome [1, 2, 3] == false
#guard isPalindrome [1, 2, 4, 8, 16, 8, 4, 2, 1] == true
#guard isPalindrome ["a", "b", "a"] == true
#guard isPalindrome ['x'] == true
