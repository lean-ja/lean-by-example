/- # slim_check

`slim_check` は、証明しようとしているゴールが間違っていないかチェックし、反例を見つけるとエラーで警告するタクティクです。 -/
import Mathlib.Tactic.SlimCheck

variable (a b : ℕ)

example (h : 2 ≤ a + b) : 1 ≤ a := by
  /-
  Found problems! というエラーが表示される
  -/
  fail_if_success slim_check

  sorry

/-!
## 反例が見つからない時

100 個のテストケースでテストしてOKならエラーにならないのですが、途中でギブアップした場合はエラーになります。-/

-- Gave up ** times と表示される
example (h : a = 1) : a ≤ 1 := by
  slim_check
