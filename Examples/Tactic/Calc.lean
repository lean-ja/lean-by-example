/- # calc

`calc` は計算モードに入るためのタクティクです．推移律が成り立つような二項関係をつなげて，一つの証明項を構成します．
-/
-- `calc` そのものは `import` なしで使える
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

variable (a b : ℝ)

example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  suffices a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 from by
    linarith
  calc a ^ 2 - 2 * a * b + b ^ 2
    _ = (a - b) ^ 2 := by ring
    _ ≥ 0 := by positivity

/- `calc` の直後に来る項も `_` で省略することができます． -/

example : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  show |x * y| < ε

  calc
    _ = |x| * |y| := abs_mul x y
    _ < ε * ε := by gcongr
    _ ≤ 1 * ε := by gcongr
    _ = ε := by norm_num
