import Mathlib.Tactic.NormNum -- `norm_num` タクティクを使うために必要

def myFun (n : ℕ) : ℕ :=
  n + 1

example (n : ℕ) : myFun n ≥ 1 := by
  -- `dsimp` でも同じことができる
  try
    dsimp [myFun]
    show n + 1 ≥ 1
    fail

  -- `myFun` を定義に展開する
  unfold myFun
  norm_num
