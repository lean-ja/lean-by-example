/- # 003 Longest Substring Without Repeating Characters

文字列 `s` が与えられたとき、重複する文字を含まない最長の（連続した）部分文字列の長さを求めなさい。
-/
import Lean
import Batteries

open Std HashSet

section Naive

/-- 文字列`s`が与えられたときに、`s`が重複する文字を含むかどうか -/
def String.hasDup (s : String) : Bool :=
  (HashSet.ofList s.toList).size < s.length

/-- `a : Nat`に対して、`i ≤ j < a`を満たすような`(i, j)`ペアのリストを返す -/
def subStrAux (a : Nat) : List (Nat × Nat) :=
  match a with
  | 0 => []
  | a + 1 =>
    let ps := subStrAux a
    -- `j = a`のペアと`j < a`のペアに分割する
    let plus1 := List.range a |>.map (fun i => (i, a))
    (a, a) :: (ps ++ plus1)

/-- 文字列`s`が与えられたときに、その部分文字列をすべて返す -/
def String.substrings (s : String) : List String := Id.run do
  let mut result : List String := []
  let idList := subStrAux s.length
  for (i, j) in idList do
    if i == j then
      -- 空文字列はいったん無視する
      continue
    let sub := s.extract ⟨i⟩ ⟨j⟩
    result := sub :: result
  return "" :: result

set_option warn.sorry false in --#

def sol (s : String) : Nat :=
  let s := s.toList
  sorry

end Naive
