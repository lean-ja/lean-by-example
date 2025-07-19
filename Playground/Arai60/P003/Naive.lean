/- # 003 Longest Substring Without Repeating Characters

文字列 `s` が与えられたとき、重複する文字を含まない最長の（連続した）部分文字列の長さを求めなさい。
-/
import Playground.Arai60.Lib

open Std HashSet

/- # 素朴な解法

シンプルに全探索する方法。

1. 単純に部分文字列をすべて列挙する
2. 重複する文字を含まないものだけ選ぶ
3. その中で最長のものを選ぶ
-/

def naive (s : String) : Nat :=
  s.allSubstrings
    |>.filter (!String.hasDup ·)
    |>.toList
    |>.map String.length
    |>.foldl max 0

private def tests : List <| @TestCase String Nat := [
  ⟨"abcabcbb", 3⟩,
  ⟨"bbbbb", 1⟩,
  ⟨"pwwkew", 3⟩,
]

#eval runTest tests naive
