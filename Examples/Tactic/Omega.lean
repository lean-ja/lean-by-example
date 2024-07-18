/- # omega

`omega` タクティクは、[「The omega test: a fast and practical integer programming algorithm for dependence analysis」](https://dl.acm.org/doi/pdf/10.1145/125826.125848)に基づいて実装されたタクティクで、整数や自然数の線形制約を扱う能力を持ちます。

似たタクティクに `linarith` がありますが, `linarith` が有理数や実数を扱うのに長けているのに対して、`omega` は自然数や整数を扱うのに長けています。
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

example (n m : Nat) : n * m = ((n + m) ^ 2 - n ^ 2 - m ^ 2 ) / 2 := by
  -- `(n + m) ^ 2` を展開する
  ring_nf

  -- `n * m` の部分は、一般の `x` に置き換えて証明してもよい
  generalize n * m = x

  -- つまり、以下を示せばよい
  show x = (x * 2 + n ^ 2 + m ^ 2 - n ^ 2 - m ^ 2) / 2

  -- これは `linarith` では示せない
  fail_if_success linarith

  -- `omega` では示せる
  omega

/-! Lean では自然数同士の引き算は整数同士の引き算とは異なる結果になって厄介なのですが、`omega` はこの問題を上手く処理します。 たとえば、以下は `linarith` では示すことができない線形な命題です。-/

variable (a b : Nat)

example (h : (a - b : Int) ≤ 0) : (a - b = 0) := by
  -- `linarith` では示すことができません
  fail_if_success linarith

  -- `omega` では示すことができます
  omega

example (h : a > 0) : (a - 1) + 1 = a := by
  fail_if_success linarith
  omega

example (h : a / 2 < b) : a < 2 * b := by
  fail_if_success linarith
  omega

example : (a - b) - b = a - 2 * b := by
  fail_if_success linarith
  omega

/-! `omega` は整数や自然数の整除関係を扱うこともできます。-/

example {a b c : ℤ} : 3 ∣ (100 * c + 10 * b + a) ↔ 3 ∣ (c + b + a) := by omega

example {a b c : ℕ} : 3 ∣ (100 * c + 10 * b + a) ↔ 3 ∣ (c + b + a) := by omega
