/- # funext

関数 `f` と `g` が等しいことを示す際に，引数 `x` をとって `f x = g x` を示そうとすることがありますが，`funext` はそれを行うタクティクです. -/
import Mathlib.Tactic.Ring -- `ring` を使用するのに必要

def f := fun (x : Nat) ↦ x + x

def g := fun (x : Nat) ↦ 2 * x

example : f = g := by
  -- 引数 `x` を取る
  funext x

  -- `f` と `g` を定義に展開する
  dsimp [f, g]

  -- `x + x` と `2 * x` が等しいことを証明する
  show x + x = 2 * x
  ring

/- なお `funext` は `ext` で置き換えることができます．-/

example : f = g := by
  -- `ext` で書き換えることができる
  ext x

  dsimp [f, g]

  ring
