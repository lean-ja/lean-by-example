import Lean

open Std HashSet

namespace String

/-- 文字列`s`が与えられたときに、`s`が重複する文字を含むかどうか -/
def hasDup (s : String) : Bool :=
  (HashSet.ofList s.toList).size < s.length

/-- 重複を除いて、すべての部分文字列を列挙する -/
def allSubstrings (s : String) : HashSet String := Id.run do
  let mut result : HashSet String := {}
  for j in [1 : s.length + 1] do
    for i in [0 : j] do
      let sub := s.extract ⟨i⟩ ⟨j⟩
      result := result.insert sub
  return result.insert ""

#guard (allSubstrings "ab").toList = ["", "a", "ab", "b"]
#guard (allSubstrings "abc").size = 7
#guard (allSubstrings "abcde").size = 16

def extractRange (s : String) (range : Range) : String :=
  s.extract ⟨range.start⟩ ⟨range.stop⟩

#guard "hello world".extractRange [0 : 5] == "hello"

/-- **TODO** GetElem の Range アクセスバージョンを作ってもらうことはできないのだろうか？ -/
instance : GetElem String Range String (fun _ _ => True) where
  getElem s range _h := s.extractRange range

#guard "hello"[[0 : 2]] = "he"

end String
