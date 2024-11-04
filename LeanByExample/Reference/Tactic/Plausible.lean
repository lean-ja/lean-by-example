/- # plausible

`plausible` は、証明しようとしているゴールが間違っていないかチェックし、反例を見つけるとエラーで警告するタクティクです。 -/
import Plausible

variable (a b : Nat)

/-- error: Found a counter-example! -/
#guard_msgs (error) in
  example (h : 0 ≤ a + b) : 1 ≤ a := by
    plausible (config := { quiet := true })

    sorry

/-
## 反例が見つからない時

100 個のテストケースでテストしてOKならエラーにならないのですが、途中でギブアップした場合はエラーになります。-/

/--
warning: Gave up after failing to generate values that fulfill the preconditions 100 times.
---
warning: declaration uses 'sorry'
-/
#guard_msgs (warning) in
  example (a : Nat) : a ≠ a → a ≤ 1 := by
    plausible
