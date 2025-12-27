/- # while

`while` は、「ある条件が成り立っている間、同じ処理を繰り返す」ための構文です。`while P do B` という構文で用いて、条件 `P` が成り立つ間、命令 `B` を繰り返し実行します。
-/

/-- 1から5までの数字をリストに詰めて返す -/
def packOneToFive : List Nat := Id.run do
  let mut result := []
  let mut n := 1
  while n ≤ 5 do
    result := result ++ [n]
    n := n + 1
  return result

#guard packOneToFive = [1, 2, 3, 4, 5]

/- ## while ループと停止性

`while` ループを使うと、停止するとは限らない計算が（停止性の証明を与えてもいないのに）書けてしまいます。たとえば以下は、述語 `P : Nat → Bool` を成り立たせる最小の自然数を探してくる関数の例です。
-/

/-- 述語 `P : Nat → Bool` を成り立たせる最小の自然数を返す -/
def searchMinExample (P : Nat → Bool) : Nat := Id.run do
  let mut n := 0
  while !P n do
    n := n + 1
  return n

#guard searchMinExample (fun n => n % 7 = 1) = 1

/-
なぜ停止性の証明が必要ないのかというと、`while` ループが内部で `Lean.Loop.forIn` という関数に展開されるのですが、これが [`partial`](#{root}/Modifier/Partial.md) で修飾された関数だからです。

したがって特に、`while` で定義された関数について何かを証明することはできません。たとえ明らかに停止する関数であっても、`while` で書かれた部分については証明不能になります。
-/

/-- 明らかに停止するし明らかに`0`しか返さないはずの関数 -/
def trivialWhile : Nat := Id.run do
  let mut m := 0
  while false do
    m := m + 1
  return m

-- 明らかなはずなのに全然証明できない
set_option warn.sorry false in --#
example : trivialWhile = 0 := by
  fail_if_success rfl
  fail_if_success try?
  sorry
