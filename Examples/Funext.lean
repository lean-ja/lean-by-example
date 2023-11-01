import Mathlib.Tactic.Ring -- `ring` を使用するのに必要

def f := fun (x : Nat) ↦ x + x

def g := fun (x : Nat) ↦ 2 * x

/-! ## funext -/

example : f = g := by
  -- 引数 `x` を取る
  funext x

  -- `f` と `g` を定義に展開する
  unfold f g

  -- `x + x` と `2 * x` が等しいことを証明する
  ring

/-! ## ext との関連 -/

example : f = g := by
  -- `ext` で書き換えることができる
  ext x

  unfold f g

  ring
