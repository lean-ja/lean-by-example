/- # unfold

`unfold` は、式の展開(unfolding)を行うタクティクです。定義に基づいて式を展開します。

何も指定しなければゴールを変形しようとします。ローカルコンテキストにある項 `h` について展開を行うには、`unfold ... at h` のように `at` を付けます。

[`dsimp`](./Dsimp.md) タクティクを使っても同様のことができます。-/

def myFun (n : Nat) : Nat :=
  n + 1

example (n : Nat) : myFun n ≥ 1 := by
  -- `dsimp` でも同じことができる
  try
    dsimp [myFun]
    show n + 1 ≥ 1
    fail

  -- `myFun` を定義に展開する
  unfold myFun
  simp
