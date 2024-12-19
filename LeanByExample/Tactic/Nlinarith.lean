/- # nlinarith

`nlinarith` は 非線形(non-linear)な式も扱えるように [`linarith`](./Linarith.md) にいくつか前処理を追加したものです。-/
import Mathlib.Tactic.Linarith -- `linarith` や `nlinarith` を使うため

variable (a b : ℕ)

example (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  -- `linarith` では示すことができない
  fail_if_success linarith

  nlinarith
