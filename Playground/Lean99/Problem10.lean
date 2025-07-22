/-
# 問題 10
(初級 🌟) 問題9の結果を使って、いわゆるランレングス符号化（連続する重複要素を (N, E) の形で圧縮する）を実装せよ。
-/
namespace P10

variable {α : Type} [BEq α] [Inhabited α]

def pack (l : List α) : List (List α) :=
  match l with
  | [] => []
  | [a] => [[a]]
  | a :: b :: t =>
    let p := pack (b :: t)
    if a != b then
      [a] :: p
    else
      ([a] ++ p.head!) :: p.tail!

def encode (l : List α) : List (Nat × α) :=
  pack l |>.map fun x => (x.length, x.head!)

#guard encode [1, 1, 2, 2, 2, 3, 4, 4, 4, 4] == [(2, 1), (3, 2), (1, 3), (4, 4)]
#guard encode ['a', 'a', 'b', 'c', 'c'] == [(2, 'a'), (1, 'b'), (2, 'c')]
#guard encode [1, 1] == [(2, 1)]

end P10
