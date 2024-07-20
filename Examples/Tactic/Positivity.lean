/- # positivity
`positivity` は、`0 ≤ x` や `0 < x` や `x ≠ 0` という形のゴールを証明するためのタクティクです。
-/
import Mathlib.Tactic

variable {a b : ℤ}

example (ha : 3 < a) : 0 ≤ a ^ 3 + a := by
  -- linarith では示せない
  fail_if_success linarith

  -- omega でも示せない
  fail_if_success omega

  positivity

example (ha : 1 < a) : 0 < |3 + a| := by
  -- linarith では示せない
  fail_if_success linarith

  -- omega でも示せない
  fail_if_success omega

  positivity

/- ゴールを構成する式がすべて数値的な下界を持つならば、`positivity` は再帰的に適用されます。-/

example : 0 ≤ max (-3) (b ^ 2) := by positivity

example : 0 < max (-3) ((1 + a) ^ 2 + 3) := by positivity

example : 0 < |2 + a| + |3 + b| + |1 + a ^ 2| := by positivity
