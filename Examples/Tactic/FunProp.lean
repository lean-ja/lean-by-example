/-
# fun_prop

`fun_prop` は、連続性や可測性など、関数に関する性質を示すタクティクです。
-/
import Mathlib.Tactic

variable {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v)

/-- 連続関数の積は連続関数 -/
example : Continuous (fun x ↦ u x * v x) := by
  fun_prop

/-- 有理関数が可測関数であることを示す -/
example : Measurable fun x : ℝ => (x * x - 1) / x + (x - x * x) := by
  fun_prop
