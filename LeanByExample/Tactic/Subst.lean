/- # subst

`subst` は、ローカルコンテキストにある等式 `x = t` や `t = x` を使って、変数 `x` を式 `t` で置き換えるタクティクです。

`rw` との違いは、`subst` が **置き換え後に変数と対応する等式をコンテキストから取り除く** 点にあります。 -/
import Mathlib.Tactic

/-- `x = y` があれば、`P x` から `P y` が言える -/
example (P : Nat → Prop) (x y : Nat) (hxy : x = y) (hx : P x) : P y := by
  -- `x` を `y` で置き換える
  subst x

  -- `x` はコンテキストから消え、`hxy` も不要になる
  guard_hyp hx : P y
  exact hx

/-- `subst` は左右が逆向きの等式でも使える -/
example (P : Nat → Prop) (x y : Nat) (hyx : y = x) (hy : P y) : P x := by
  subst y
  guard_hyp hy : P x
  exact hy

/-- 目的の変数を明示しない `subst` は、置き換え可能な等式を使って進める -/
example (x y z : Nat) (h1 : x = y) (h2 : y = z) : x = z := by
  subst
  rfl
