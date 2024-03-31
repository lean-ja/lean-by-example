/- # convert

ローカルコンテキストに現在のゴールに近いけれども等しくはない `h` があるとき，`exact h` としても失敗します．しかし `convert h` は成功する可能性があり，成功した場合は `h` とゴールの差分を新たなゴールとします．-/
import Mathlib.Tactic.Convert

variable (a b c: Nat)

example (f : Nat → Nat) (h : f (a + b) = 0) (hc: a + b = c) : f (c) = 0 := by
  -- `h` はゴールと等しくないので失敗する
  fail_if_success exact [h]

  -- `h` とゴールの差分を新たなゴールにする
  convert h

  -- ゴールが `⊢ c = a + b` に変わっている
  show c = a + b

  rw [hc]
