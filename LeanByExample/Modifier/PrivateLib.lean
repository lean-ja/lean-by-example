-- PrivateLib.lean の内容

structure Point where
  x : Nat
  y : Nat

namespace Point

  protected def sub (p q : Point) : Point :=
      { x := p.x - q.x, y := p.y - q.y }

  private def private_sub := Point.sub

end Point
