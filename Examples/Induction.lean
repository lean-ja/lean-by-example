import Mathlib.Algebra.Algebra.Basic -- `simp` で使う
import Mathlib.Init.Data.Nat.Lemmas -- 強い帰納法のために必要
import Mathlib.Order.Basic -- `simp` で使う
import Mathlib.Tactic.Cases -- `induction'` のために必要

/-! ## 帰納法をいつ使うか -/

namespace Induction

-- 自然数の定義を `#print` コマンドで調べてみる

/-
inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : ℕ (ゼロは自然数)
Nat.succ : ℕ → ℕ (`n` が自然数なら `succ n` も自然数)
-/
#print Nat

-- 自然数はこのように帰納的に定義されているので，
-- 自然数に対して何かを示そうとすると帰納法を使うことが自然な選択といえる
-- 一般に， `inductive` などで帰納的に定義されたものを扱うとき
-- 帰納法が有用な可能性は高い

/-! ## induction -/

/-- 階乗関数 -/
def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example (n : Nat) : 0 < fac n := by
  -- `n` についての帰納法で示す
  induction n with

  | zero =>
    simp [fac]

  | succ n ih =>
    simpa [fac]

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
    simp [fac]

  case succ =>
    simpa [fac]

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

  時には， より強い帰納法が必要なこともあります． 強い帰納法とは， たとえば

  * `P(0)` を示す
  * `(∀ k < n, P (k)) → P (n)` を示す
  * したがって `∀ n, P (n)` である

  という形式で表されるような帰納法のことです．
  これは超限帰納法の特別な場合です．
-/

/-- フィボナッチ数列の通常の定義をそのまま Lean の関数として書いたもの -/
def fibonacci : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fibonacci n + fibonacci (n + 1)

/-- フィボナッチ数列の線形時間の実装 -/
def fib (n : Nat) : Nat :=
  (loop n).1
where
  loop : Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 =>
      let p := loop n
      (p.2, p.1 + p.2)

/-- `fib` が `fibonacci` と同じ漸化式を満たすことを証明する -/
@[simp]
theorem fib_add (n : Nat) : fib n + fib (n + 1) = fib (n + 2) := by rfl

/-- `fibonacci` と `fib` は同じ結果を返す -/
example : fibonacci = fib := by
  -- 関数が等しいことを示すので，引数 `n` が与えられたとする
  ext n

  -- `n` についての強い帰納法で示す
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => simp_all [fibonacci]

end Induction
