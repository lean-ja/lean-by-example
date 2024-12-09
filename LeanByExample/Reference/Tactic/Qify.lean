/- # qify
`qify` は自然数や整数に関する命題を有理数に関する命題にキャストします。
-/
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Qify -- `qify` を使うために必要

example (x : Nat) (h : x ≥ 1) : 2 * x ≥ 2 := by
  -- 自然数から有理数にキャストする
  qify at h ⊢

  -- 次の状態になる
  guard_hyp h : 1 ≤ (x : ℚ)
  show (2 : ℚ) ≤ 2 * x

  calc
    (2 : ℚ) = 2 * 1 := by simp
    _ ≤ 2 * (x : ℚ) := by gcongr

/- ## 用途

自然数や整数は体ではないので、体を想定したタクティクが使えないことがあります。
`qify` で有理数にキャストすることで、そのようなタクティクが使えるようになり、証明が楽になることがあります。
-/

example (n m : Nat) (x : Rat) (hx : x > 0) (h : n * m = x) : m > 0 := by
  -- 最初は `nlinarith` が使えない
  fail_if_success nlinarith

  -- 有理数にキャストする
  qify

  -- `nlinarith` が使えるようになった！
  nlinarith
