/- # 003 Longest Substring Without Repeating Characters

文字列 `s` が与えられたとき、重複する文字を含まない最長の（連続した）部分文字列の長さを求めなさい。
-/
import Playground.String

open Std HashSet

structure TestCase where
  input : String
  expected : Nat

private def tests : List TestCase := [
  ⟨"abcabcbb", 3⟩,
  ⟨"bbbbb", 1⟩,
  ⟨"pwwkew", 3⟩,
]

def runTest (tests : List TestCase) (f : String → Nat) : IO Unit := do
  for test in tests do
    let actual := f test.input
    if actual != test.expected then
      IO.println s!"Test failed for input `{test.input}`: expected {test.expected}, got {actual}"
      return
  IO.println s!"All tests passed!"

/- # 素朴な解法

シンプルに全探索する方法。

1. 単純に部分文字列をすべて列挙する
2. 重複する文字を含まないものだけ選ぶ
3. その中で最長のものを選ぶ
-/
section Naive

def naive (s : String) : Nat :=
  s.allSubstrings
    |>.filter (fun sub => !String.hasDup sub)
    |>.toList
    |>.map (fun sub => sub.length) -- **TODO** HashSet には map がないのか？？
    |>.foldl max 0

#eval runTest tests naive

end Naive
