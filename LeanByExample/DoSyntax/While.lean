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

/-- 述語 `P : Nat → Bool` を成り立たせる最小の自然数を返す。
`P` が成り立つ要素が存在する保証はないので停止するとは限らない。 -/
def searchMinExample (P : Nat → Bool) : Nat := Id.run do
  let mut n := 0
  while !P n do
    n := n + 1
  return n

#guard searchMinExample (fun n => n > 5) = 6

/-
これは暗黙的に [`partial`](#{root}/Modifier/Partial.md) で修飾された関数を利用していることを想像させますが、実際には違います。`while` ループで書かれた関数について何かを証明することは可能です。
-/

/-- 明らかに停止するし明らかに`0`しか返さない関数 -/
def trivialWhile : Nat := Id.run do
  let mut m := 0
  while false do
    m := m + 1
  return m

-- `while false` の本体は実行されないので、結果は初期値のままになる
example : trivialWhile = 0 := by
  unfold trivialWhile
  simp only [ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp
