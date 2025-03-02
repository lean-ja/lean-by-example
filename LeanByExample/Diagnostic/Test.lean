/- # \#test
`#test` コマンドは、Plausible ライブラリで定義されているもので、与えられた命題が成り立つかどうか、具体例をランダムに生成してチェックすることで検証します。[`plausible`](#{root}/Tactic/Plausible.md) タクティクと同様の機能を持ちます。[^erickson]
-/
import Plausible

/-- 農民の掛け算と呼ばれるよくわからない関数 -/
def peasantMul (x y : Nat) : Nat := Id.run do
  let mut x := x
  let mut y := y
  let mut prod := 0
  while x > 0 do
    if x % 2 = 1 then
      prod := prod + y
    x := x / 2
    y := y * 2
  return prod

-- どうやら a * b と等しいようだが…？
-- これは本当に正しいのだろうか
#guard peasantMul 3 2 = 6
#guard peasantMul 2 4 = 8

-- 正しそう！
#test ∀ n m, peasantMul n m = n * m

/- `#test` コマンドを使う利点としては、期待される仕様をそのまま表現したものがテストとして機能するので、テストを作る労力が軽減されるというのがあります。仕様を述語論理で表現することが容易な関数のテストや、異なる実装をした関数同士が実は等しいといったテストで有用でしょう。 -/

/-- 与えられたリストに含まれない最小の要素を求める -/
def minFree (xs : List Nat) : Nat :=
  List.range (xs.length + 2)
    |>.removeAll xs
    |>.head!

-- `minFree`の出力は元のリストに含まれない
#test ∀ xs : List Nat, minFree xs ∉ xs

-- `minFree`の出力は、元のリストに含まれない数の集合に対して下界を与える
#test ∀ xs : List Nat, ∀ x : Nat, x ∉ xs → minFree xs ≤ x

/- [^erickson]: 以下に紹介する `peasantMul` 関数の例は、Jeff Erickson「Algorithms」の0章2節で紹介されているアルゴリズムを参考にさせていただきました。 -/
