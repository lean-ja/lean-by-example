/-
# induction'

`induction'` は `induction` の Lean 3 での構文を残したバージョンです。
-/
import Mathlib.Tactic -- 大雑把に import する

namespace InductionAp --#

/-- `0` から `n` までの和を計算する.
多項式関数として表現する都合で、返り値は `Rat` にしてある. -/
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
    -- `sum` の定義を展開し、帰納法の仮定を適用する
    simp [sum, ih]

    -- 後は可換環の性質から示せる
    ring

/-!
### 〇〇の～についての帰納法

関数適用した対象に対する帰納法も行うことができます。

以下の例は, Cantor の対関数 `pair : ℕ × ℕ → ℕ` に対して逆写像 `unpair : ℕ → ℕ × ℕ` が存在することを示しています。証明の中で `pair (m, n)` に対する帰納法を行っています。また、`generalizing` 構文を使うことで、帰納法の仮定の中の変数を全称化する工夫も行っています。
-/
namespace Pair --#

/-- `0` から `n` までの自然数の和.
多項式として表現する必要はないので、返り値は自然数. -/
def sum (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => (n + 1) + sum n

@[simp]
theorem summ_zero_iff_zero {n : ℕ} : sum n = 0 ↔ n = 0 := by
  constructor <;> intro h
  case mp =>
    induction' n with n _ih <;> simp at *
    simp [sum] at h
  case mpr =>
    rw [h, sum]

/-- カントールの対関数 -/
def pair : ℕ × ℕ → ℕ
  | (m, n) => sum (m + n) + m

@[simp]
theorem pair_zero : pair 0 = 0 := by rfl

/-- カントールの対関数の逆関数 -/
def unpair : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | x + 1 =>
    let (m, n) := unpair x
    if n = 0 then
      (0, m + 1)
    else
      (m + 1, n - 1)

@[simp]
theorem unpair_zero : unpair 0 = 0 := by rfl

theorem unpair_pair_eq_id (m n : ℕ) : unpair (pair (m, n)) = (m, n) := by
  -- `x = pair (m, n)` として `x` に対する帰納法を利用する
  induction' h : pair (m, n) with x ih generalizing m n
  all_goals simp at *

  -- `pair (m, n) = 0` のとき
  case zero =>
    -- `pair` の定義から明らか。
    simp [pair] at h
    aesop

  -- `pair (m, n) = x + 1` のとき
  case succ =>
    -- `m` がゼロかそうでないかで場合分けする
    match m with

    -- `m = 0` のとき
    | 0 =>
      -- `pair (0, n) = x + 1` により `n > 0` が成り立つ.
      have npos : n > 0 := by
        by_contra!; simp at this
        simp [this] at h
        contradiction

      -- よって `n = (n - 1) + 1` であり、
      replace npos : n = (n - 1) + 1 := by omega
      have : sum n = sum (n - 1) + n := by
        nth_rw 1 [npos]
        dsimp [sum]
        omega

      -- `pair (n - 1, 0) = x` が成り立つ.
      replace : pair (n - 1, 0) = x := by
        dsimp [pair] at h ⊢
        simp at h
        rw [this] at h
        omega

      -- 後は帰納法の仮定から従う.
      specialize ih (n-1) 0 this
      simp [unpair, ih]
      symm; assumption

    -- `m = m' + 1` のとき
    | m' + 1 =>
      -- `pair` の定義から `pair (m', n + 1) = x` が成り立つ。
      have : pair (m', n + 1) = x := by
        simp [pair] at h ⊢
        rw [show m' + 1 + n = m' + (n + 1) from by ac_rfl] at h
        omega

      -- 後は帰納法の仮定から従う。
      specialize ih m' (n + 1) this
      simp [unpair, ih]

end Pair --#

/-!
## 完全帰納法

時には、 より強い帰納法が必要なこともあります。 強い帰納法とは、 たとえば

* `∀ n, (∀ k < n, P (k)) → P (n)` を示す
* したがって `∀ n, P (n)` である

という形式で表されるような帰納法のことです。
これは超限帰納法の特別な場合で、完全帰納法や累積帰納法とも呼ばれます。
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
  -- 関数が等しいことを示すので、引数 `n` が与えられたとする
  ext n

  -- `n` についての強い帰納法で示す
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => simp_all [fibonacci]

end InductionAp --#
