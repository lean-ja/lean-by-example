/- # fin_cases

`fin_cases` は有限通りの場合分けを行うタクティクです.
何度も `cases` をしないと全通りに場合分けできない場合でも, 一発で全てのケースを生成することができます.
-/

/-
`h : x ∈ [a₁, ..., aₙ]` といった形の仮定に対して `fin_cases h` とすると, 代入 `x = a₁`, ..., `x = aₙ` を施した n 個のゴールが生成されます.
-/

import Mathlib.Tactic.FinCases

example {n : ℕ} (h : n ∈ [2, 4, 42]) : 2 ∣ n := by
  fin_cases h
  /-
  n に 2, 4, 42 を順に代入した

  ⊢ 2 ∣ 2
  ⊢ 2 ∣ 4
  ⊢ 2 ∣ 42

  の 3 つのゴールが生じる
  -/
  -- あとはそれぞれのゴールに対して具体的に計算して証明する
  all_goals decide

/-
`fin_cases` を使わない場合, 以下のように `cases` を繰り返し用いて一つずつケースを取り出すことになります.
-/

example {n : ℕ} (h : n ∈ [2, 4, 42]) : 2 ∣ n := by
  cases h
  case head =>
    show 2 ∣ 2; decide
  case tail h => -- h : n ∈ [4, 42]
    cases h
    case head =>
      show 2 ∣ 4; decide
    case tail h => -- h : n ∈ [42]
      cases h
      case head =>
        show 2 ∣ 42; decide
      case tail h => -- h : n ∈ []
        cases h

/-
`fin_cases` は `List α` のほかに, `Finset α` と `Multiset α` に対して適用可能です.
-/

example {n : ℕ} (h : n ∈ ({2, 4, 42} : Finset ℕ)) : 2 ∣ n := by
  fin_cases h
  all_goals decide

example {n : ℕ} (h : n ∈ ({2, 4, 42} : Multiset ℕ)) : 2 ∣ n := by
  fin_cases h
  all_goals decide

/-
また, 型 `α` が「有限な型」である(インスタンス `Fintype α` が実装されている)場合, `fin_cases x` は `x : α` のとりうる値に関する場合分けを行います.
-/

-- `Fin n` は 0 から n-1 までの整数からなる型で, val : ℕ と isLt : val < n の 2 つのフィールドを持つ
example (n : Fin 10) (h : n.val ∣ 6) : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
  -- n.val = 0, ..., n.val = 9 の 10 通りに場合分けする
  fin_cases n

  -- h : n.val ∣ 6 が成り立たないケースは contradiction で示される
  any_goals contradiction

  -- 残りのケースについて, n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 が成り立つ
  all_goals decide
