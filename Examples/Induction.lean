import Mathlib.Algebra.Algebra.Basic -- `simp` で使う
import Mathlib.Init.Data.Nat.Lemmas -- 強い帰納法のために必要
import Mathlib.Order.Basic -- `simp` で使う
import Mathlib.Tactic.Cases -- `induction'` のために必要
import Mathlib.Tactic.Says -- `says` のために必要

/-! ## 帰納法をいつ使うか -/

namespace Examples -- 名前被りを避けるため

  -- 自然数の定義
  inductive Nat
    /-- `zero` は自然数 -/
    | zero : Nat

    /-- `n` が自然数なら `succ n` も自然数 -/
    | succ (n : Nat) : Nat

  -- 自然数はこのように帰納的に定義されているので，
  -- 自然数に対して何かを示そうとすると帰納法を使うことが自然な選択といえる
  -- 一般に，`inductive` などで帰納的に定義されたものを扱うとき
  -- 帰納法が有用な可能性は高い

end Examples

/-! ## induction -/

/-- 階乗関数 -/
def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example (n : Nat) : 0 < fac n := by
  -- `n` についての帰納法で示す
  induction n with

  | zero =>
    simp only [fac]

  | succ n ih =>
    simp? [fac] says
      simp only [
        fac,
        gt_iff_lt,
        add_pos_iff,
        or_true,
        zero_lt_mul_left
      ]
    assumption

/-!
  ## inudction'

  `induction'` というタクティクもあります．
  これは Lean3 における `induction` タクティクとより構文が似ていて，
  高度な帰納法が可能です．
-/

example (n : Nat) : 0 < fac n := by
  -- `ih` は帰納法の仮定
  -- `k` は `ih` に登場する変数
  induction' n with k ih

  case zero =>
    simp only [fac]

  case succ =>
    simp? [fac] says
      simp only [
        fac,
        gt_iff_lt,
        add_pos_iff,
        or_true,
        zero_lt_mul_left
      ]
    assumption

/-!
  ### 〇〇の～についての帰納法

  `induction'` では「リストの長さに対する帰納法」もできます．
-/

variable (α : Type)

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

/-!
  ### 強い帰納法

  時には，より強い帰納法が必要なこともあります．強い帰納法とは，たとえば

  * `P(0)` を示す
  * `(∀ k < n, P (k)) → P (n)` を示す
  * したがって `∀ n, P (n)` である

  という形式で表されるような帰納法のことです．
  これは超限帰納法の特別な場合です．
-/

variable (P : Nat → Prop)

example (n : Nat) : P n := by
  -- `n` についての強い帰納法で示す
  induction' n using Nat.strong_induction_on with n ih

  -- 仮定が追加される
  guard_hyp ih : ∀ (m : ℕ), m < n → P m

  match n with
  | 0 => sorry
  | k + 1 => sorry
