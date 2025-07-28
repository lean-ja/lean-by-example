import Lean

open Std

/--
関数型スタイルでの文字カウント関数。
`s.toList.foldl` により、文字の出現回数を `HashMap` に蓄積していく。

**TODO** この関数に対して基本的な性質を証明することはできるか？
-/
def String.countingChars (s : String) : HashMap Char Nat :=
  s.toList.foldl
    (fun acc c => acc.insert c (acc.getD c 0 + 1))
    (init := {})

@[simp]
theorem String.countNull : String.countingChars "" = {} := by
  constructor

/--
関数型スタイルでの firstUniqueChar 実装。
zipWithIndex によって文字とそのインデックスを対応させ、出現回数が 1 の最初のものを探す。
-/
def firstUniqueChar (s : String) : Option Nat :=
  let counts := String.countingChars s
  s.toList.zipIdx.find? (fun (c, _) => counts[c]! == 1) |>.map Prod.snd

#guard firstUniqueChar "leetcode"     == some 0
#guard firstUniqueChar "loveleetcode" == some 2
#guard firstUniqueChar "aabb"         == none
#guard firstUniqueChar ""             == none
#guard firstUniqueChar "abcabcde"     == some 6
