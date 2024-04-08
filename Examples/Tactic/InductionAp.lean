/-
# induction'

`induction'` は `induction` の Lean 3 での構文を残したバージョンです．
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Cases -- `induction'` のために必要

namespace InductionAp

/-- `1` から `n` までの和を計算する関数 -/
def sum (n : Nat) : Rat :=
  match n with
  | 0 => 0
  | n + 1 => (n + 1) + sum n

example (n : Nat) : sum n = n * (n + 1) / 2 := by
  -- `n` についての帰納法で示す
  induction' n with n ih

  -- `n = 0` の場合
  case zero =>
    simp_all [sum]

  -- `0` から `n` までの自然数で成り立つと仮定する
  case succ =>
    -- `sum` の定義を展開し，帰納法の仮定を適用する
    simp [sum, ih]

    -- 後は可換環の性質から示せる
    ring

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
## 完全帰納法

時には， より強い帰納法が必要なこともあります． 強い帰納法とは， たとえば

* `∀ n, (∀ k < n, P (k)) → P (n)` を示す
* したがって `∀ n, P (n)` である

という形式で表されるような帰納法のことです．
これは超限帰納法の特別な場合で，完全帰納法や累積帰納法とも呼ばれます．
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

end InductionAp
