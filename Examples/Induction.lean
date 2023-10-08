-- `induction'` のために必要
import Mathlib.Tactic.Cases

import Mathlib.Tactic.Positivity

namespace Examples

-- ANCHOR: nat
inductive Nat
  | zero : Nat
  | succ (n : Nat) : Nat
-- ANCHOR_END: nat

end Examples

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


-- ANCHOR: strong
variable (P : Nat → Prop)

example (n : Nat) : P n := by
  -- `n` についての強い帰納法で示す
  induction' n using Nat.strong_induction_on with n ih

  -- 仮定が追加される
  guard_hyp ih : ∀ (m : ℕ), m < n → P m

  match n with
  | 0 => sorry
  | k + 1 => sorry
-- ANCHOR_END: strong