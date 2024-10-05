/- # induction

`induction` は、帰納法のためのタクティクです。

たとえば、Lean では自然数 `Nat` は

* 0 は自然数
* `succ : Nat → Nat` という関数がある。つまり `n` が自然数ならば `succ n` も自然数

というように帰納的に定義されています。このように帰納的に定義されたものに対して何か証明しようとしているとき、帰納法を使うことが自然な選択になります。
-/
import Mathlib.Tactic.Ring -- `ring` を使うため

namespace Induction --#

/-- `1` から `n` までの和を計算する関数 -/
def sum (n : Nat) : Rat :=
  match n with
  | 0 => 0
  | n + 1 => (n + 1) + sum n

example (n : Nat) : sum n = n * (n + 1) / 2 := by
  -- `n` についての帰納法で示す
  induction n with

  -- `n = 0` の場合
  | zero =>
    simp [sum]

  -- `0` から `n` までの自然数で成り立つと仮定する
  | succ n ih =>
    -- `sum` の定義を展開し、帰納法の仮定を適用する
    simp [sum, ih]

    -- 後は可換環の性質から示せる
    ring

/-! ## 再帰定理
Lean では、実は帰納法を使用するのに必ずしも `induction` は必要ありません。場合分けの中で示されたケースを帰納法の仮定として使うことができます。これは recursive theorem(再帰定理) と呼ばれることがあります。[^recursive]
-/

theorem sum_exp (n : Nat) : sum n = n * (n + 1) / 2 := by
  match n with

  -- `n = 0` の場合
  | 0 => simp [sum]

  -- `0` から `n` までの自然数で成り立つと仮定する
  | n + 1 =>
    -- 仮定から、`n` について成り立つ
    have ih := sum_exp n

    -- 仮定を適用して展開する
    simp [sum, ih]

    -- 後は可換環の性質から示せる
    ring

/- `have` で宣言された命題の証明の中では、この方法は使用できません。-/
#guard_msgs (drop warning) in --#

theorem sample : True := by
  have h : ∀ n, sum n = n * (n + 1) / 2 := by
    intro n
    match n with
    | 0 => simp [sum]
    | n + 1 =>
      -- h 自身を参照することができない
      fail_if_success have ih := h n
      sorry
  trivial

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
example (n : Nat) : fibonacci n = fib n := by
  -- `n` についての強い帰納法で示す
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    -- `n = 0` の場合
    | 0 => rfl

    -- `n = 1` の場合
    | 1 => rfl

    -- `0` から `n` までの自然数で成り立つとして、`n + 2` について示す
    | n + 2 =>
      -- フィボナッチ数列の定義に基づいて展開する
      dsimp [fibonacci]

      -- `fib` の漸化式を適用する
      rw [← fib_add]

      -- 帰納法の仮定から、`n` と `n + 1` については成り立つ
      have ih_n := ih n
      have ih_succ := ih $ n + 1

      -- 帰納法の仮定を適用して示す
      simp [ih_n, ih_succ]

/-! なお、完全帰納法も `induction` タクティクを使わずに行うことができます。-/

/-- `fibonacci` と `fib` は同じ結果を返す -/
theorem fib_eq (n : Nat) : fibonacci n = fib n := by
  -- `n` についての強い帰納法で示す
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 =>
    -- フィボナッチ数列の定義に基づいて展開する
    dsimp [fibonacci]

    -- `fib` の漸化式を適用する
    rw [← fib_add]

    -- 帰納法の仮定から、`n` と `n + 1` については成り立つ
    have ih_n := fib_eq n
    have ih_succ := fib_eq $ n + 1

    -- 帰納法の仮定を適用して示す
    simp [ih_n, ih_succ]

/- ## 帰納原理の自動生成
再帰的な関数 `foo` を定義すると、その裏で Lean が帰納原理(induction principle) `foo.induct` を生成します。こうして生成された帰納原理は、`induction .. using foo.induct` という構文で使用することができます。
-/

-- `fibonacci` 関数に対して自動生成された帰納法の原理
#print fibonacci.induct

example {n : Nat} : fibonacci n = fib n := by
  induction n using fibonacci.induct

  case case1 =>
    rfl

  case case2 =>
    rfl

  case case3 n ih1 ih2 =>
    simp [fibonacci, ih1, ih2]

/- 帰納原理が生成されるのは再帰的な関数のみです。再帰的でない関数には生成されません。-/

def bar : Nat → Nat
  | 0 => 0
  | _ => 1

#guard_msgs (drop warning) in --#
#check_failure bar.induct

end Induction --#

/-
[^recursive]: [lean公式ブログの Functional induction についての記事](https://lean-lang.org/blog/2024-5-17-functional-induction/) で recursive theorem という言葉が使われています。
-/
