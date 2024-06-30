/-
# protected
`protected` は，ある名前空間 `Hoge` にある定義 `foo` に対して，必ずフルネームの `Hoge.foo` でアクセスすることを強要するものです．
-/
structure Point where
  x : Nat
  y : Nat

namespace Point

  protected def sub (p q : Point) : Point :=
    { x := p.x - q.x, y := p.y - q.y }

  -- private のテスト用の宣言
  private def private_sub := Point.sub

  -- 名前空間の中にいても，短い名前ではアクセスできない
  #check_failure sub

  -- フルネームならアクセスできる
  #check Point.sub

end Point

open Point

-- 名前空間を開いていても，短い名前でアクセスできない
#check_failure sub

-- フルネームならアクセスできる
#check Point.sub
