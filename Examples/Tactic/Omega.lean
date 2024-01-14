/- # omega

`omega` タクティクは，[「The omega test: a fast and practical integer programming algorithm for dependence analysis」](https://doi.org/10.1145/125826.125848)に基づいて実装されたタクティクで，整数や自然数の線形制約を扱う能力を持ちます．

似たタクティクに `linarith` がありますが, `omega` は前処理が強力です．Lean では自然数同士の引き算は整数同士の引き算とは異なる結果になって厄介なのですが，`omega` はこれを上手く処理します． -/
import Mathlib.Tactic.Linarith
import Std.Tactic.Omega

variable (a b : Nat)

example (h : (a - b : Int) ≤ 0) : (a - b = 0) := by
  -- `linarith` では示すことができません
  try linarith

  -- `omega` では示すことができます
  omega

example (h : a > 0) : (a - 1) + 1 = a := by
  try linarith
  omega

example (h : a / 2 < b) : a < 2 * b := by
  try linarith
  omega

example : (a - b) - b = a - 2 * b := by
  try linarith
  omega
