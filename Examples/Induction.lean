import Mathlib.Tactic.Cases -- `induction'` のために必要
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

variable (α : Type)

-- ANCHOR: induction_on_length
example (l : List α) (P : List α → Prop) : P l := by
  -- リストの長さに対する帰納法
  induction' h : l.length generalizing l

  case zero =>
    -- リストの長さが 0 のとき
    guard_hyp h: List.length l = 0

    show P l
    sorry

  case succ n IH =>
    -- リストの長さが `n + 1` のとき
    guard_hyp h: List.length l = n + 1

    -- 帰納法の仮定が使える
    guard_hyp IH: ∀ (l : List α), List.length l = n → P l

    show P l
    sorry
-- ANCHOR_END: induction_on_length

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
