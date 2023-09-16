-- `funext` 自体は mathlib に依存しないが，例のために必要
import Mathlib.Tactic

-- ANCHOR: first
def f := fun (x : Nat) ↦ x + x

def g := fun (x : Nat) ↦ 2 * x

example : f = g := by
  -- 引数 `x` を取る
  funext x

  -- `f x` と `g x` を展開する
  dsimp [f, g]

  -- `x + x` と `2 * x` が等しいことを証明する
  ring
-- ANCHOR_END: first
