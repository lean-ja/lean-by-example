/- # norm_cast

`norm_cast` は、型キャスト（ある型からある型への変換）と型強制を簡約するタクティクです。

詳細については論文 [「Simplifying Casts and Coercions」](https://arxiv.org/abs/2001.10594) などを参照してください。
-/
import Mathlib.Tactic

-- `x, m, n` は自然数とする
variable (x m n : ℕ)

example (left : (x : ℝ) < ↑m + ↑n) (right : ↑m + ↑n < (x : ℝ) + 1) : False := by
  -- `linarith` では示すことができない
  fail_if_success linarith

  -- `omega` でも示すことができない
  fail_if_success omega

  -- 仮定の `left` と `right` は実数上の不等式だが、
  -- 自然数上の不等式と解釈できるはずである。
  -- `norm_cast` はそれを実行してくれる。
  norm_cast at left right

  -- 仮定が自然数における不等式に変わった！
  guard_hyp left : x < m + n
  guard_hyp right : m + n < x + 1

  -- 後は `omega` で示せる
  omega
