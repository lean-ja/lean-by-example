/-
# induction'

`induction'` は [`induction`](./Induction.md) タクティクの構文が異なるバージョンです。
-/
import Mathlib.Tactic -- 大雑把に import する

/-- `0` から `n` までの和を計算する。
多項式関数として表現する都合で、返り値は `Rat` にしてある。-/
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

/-
## 完全帰納法

時には、より強い帰納法が必要なこともあります。 強い帰納法とは、 たとえば以下のような形式で表されるような帰納法のことです。

* `∀ n, (∀ k < n, P (k)) → P (n)` を示す。
* したがって `∀ n, P (n)` である。

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
