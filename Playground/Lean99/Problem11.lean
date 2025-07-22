/-
# 問題 11
(初級 🌟) [問題10](./Problem10.md)の結果を修正し、重複のない要素はそのまま結果リストにコピーし、重複がある要素のみ (N E) 形式にせよ。
-/
namespace P11

variable {α : Type} [BEq α]

inductive Data (α : Type) where
  | multiple : Nat → α → Data α
  | single : α → Data α
deriving Repr, DecidableEq

open Data

partial def encodeModified (l : List α) : List (Data α) :=
  match l with
  | [] => []
  | x :: _xs =>
    let (as, bs) := l.span (· == x)
    if as.length > 1 then
      multiple as.length x :: encodeModified bs
    else
      single x :: encodeModified bs

#guard encodeModified ['a', 'a', 'b', 'c'] == [multiple 2 'a', single 'b', single 'c']
#guard encodeModified ([] : List Nat) == []
#guard encodeModified ['a', 'b', 'b', 'b', 'c', 'b', 'b'] == [single 'a', multiple 3 'b', single 'c', multiple 2 'b']

end P11
