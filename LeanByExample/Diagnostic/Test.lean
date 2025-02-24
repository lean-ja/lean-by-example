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
/- [^erickson]: 以下に紹介する `peasantMul` 関数の例は、Jeff Erickson「Algorithms」の0章2節で紹介されているアルゴリズムを参考にさせていただきました。 -/
