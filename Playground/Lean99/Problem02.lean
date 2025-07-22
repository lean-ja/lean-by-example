/-
# 問題 2
(初級 🌟) リストの最後から2番目（または2番目に最後）の要素を求めよ。
-/
variable {α : Type}

def myButLast (l : List α) : Option α :=
  if l.length < 2 then
    -- `l` の長さが2未満のときでも `i` は定義できてしまうので，
    -- この if 式が必要
    none
  else
    let i := l.length - 2;
    l[i]?

#guard myButLast [1, 2, 3, 4] == some 3
#guard myButLast ['x', 'y', 'z'] == some 'y'
#guard myButLast [1] == none
