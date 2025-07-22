/-
# 問題 13
(中級 🌟🌟) ランレングス符号化を直接実装せよ。問題9のように重複部分のサブリストを明示的に作らず、カウントだけを行うこと。問題11のように (1 X) は X に簡約せよ。
-/
namespace P13

variable {α : Type} [BEq α] [Inhabited α]

inductive Data (α : Type) where
  | multiple : Nat → α → Data α
  | single : α → Data α
deriving Repr, BEq

open Data

def encodeDirect (l : List α) : List (Data α) :=
  counting l |>.map fun (n, a) =>
    if n == 1 then
      single a
    else
      multiple n a
where
  counting : List α → List (Nat × α)
    | [] => []
    | [a] => [(1, a)]
    | a :: b :: t =>
      if a != b then
        (1, a) :: counting (b :: t)
      else
        let (n, a) := counting (b :: t) |>.head!
        (n + 1, a) :: (counting (b :: t) |>.tail!)

#guard encodeDirect ['a', 'a', 'b', 'c'] == [multiple 2 'a', single 'b', single 'c']
#guard encodeDirect ['a', 'b', 'b', 'b', 'c', 'b', 'b'] == [single 'a', multiple 3 'b', single 'c', multiple 2 'b']

end P13
