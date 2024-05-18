/- # qify
`qify` は自然数や整数に関する命題を有理数に関する命題にキャストします．
-/
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Qify -- `qify` を使うために必要
import Mathlib.Tactic.Ring

variable (a b c x y z : ℕ)

example (h : x ≥ 1) : 2 * x ≥ 2 := by
  -- 自然数から有理数にキャストする
  qify at h ⊢

  -- 次の状態になる
  guard_hyp h : 1 ≤ (x : ℚ)
  show (2 : ℚ) ≤ 2 * x

  calc
    (2 : ℚ) = 2 * 1 := by rfl
    _ ≤ 2 * (x : ℚ) := by gcongr

/- より自然な例として，次の例も挙げておきます．-/

/-- `0` から `n` までの自然数の総和 -/
def sum (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (n + 1) + sum n

@[simp]
theorem sum_zero : sum 0 = 0 := by rfl

/-- 和を計算する多項式．割り算を含むので返り値が `Rat` になっている -/
def sumPoly (n : Nat) : Rat := n * (n + 1) / 2

/-- `sumPoly` が `sum` と同じ漸化式を満たす -/
theorem sumPoly_succ {n : Nat} : sumPoly (n + 1) = (n + 1) + sumPoly n := by
  simp [sumPoly]
  ring

@[simp]
theorem sumPoly_zero : sumPoly 0 = 0 := by rfl

/-- `sumPoly` の値は常に自然数で，`sum` と一致する -/
theorem sum_eq_sumPoly {n : Nat} : sum n = sumPoly n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum, sumPoly_succ, ← ih]
    qify
