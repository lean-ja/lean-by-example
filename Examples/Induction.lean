-- `induction'` のために必要
import Mathlib.Tactic.Cases

import Mathlib.Tactic.Positivity


-- ANCHOR: first
-- 階乗関数
def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example (n : Nat) : 0 < fac n := by
  -- `n` についての帰納法で示す
  induction n with
  | zero =>
    -- `fac` の定義から従う
    simp [fac]
  | succ n ih =>
    -- `fac` の定義から従う
    simp [fac]
    positivity
-- ANCHOR_END: first


-- ANCHOR: dash
example (n : Nat) : 0 < fac n := by
  -- `ih` は帰納法の仮定
  -- `k` は `ih` に登場する変数
  induction' n with k ih
  · simp [fac]
  · simp [fac]
    positivity
-- ANCHOR_END: dash
