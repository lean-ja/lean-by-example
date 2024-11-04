/- # plausible

`plausible` は、証明しようとしているゴールが間違っていないかチェックし、反例を見つけるとエラーで警告するタクティクです。 -/
import Plausible

variable (a b : Nat)

#guard_msgs (drop warning) in --#
example (h : 0 ≤ a + b) : 1 ≤ a := by
  /-
  Found problems! というエラーが表示される
  -/
  fail_if_success plausible

  sorry

/-
## 反例が見つからない時

100 個のテストケースでテストしてOKならエラーにならないのですが、途中でギブアップした場合はエラーになります。-/

-- Gave up ** times と表示される
#guard_msgs (drop warning) in --#
example (h : a = 1) : a ≤ 1 := by
  plausible
