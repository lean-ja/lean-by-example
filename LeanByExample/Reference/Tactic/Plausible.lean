/- # plausible

`plausible` は、証明しようとしているゴールが間違っていないかランダムに例を生成してチェックし、反例を見つけるとエラーで警告するタクティクです。 -/
import Plausible

variable (a b : Nat)

/-- error: Found a counter-example! -/
#guard_msgs (error) in
  example (h : 0 ≤ a + b) : 1 ≤ a := by
    plausible (config := { quiet := true })

    sorry

/-
100 個のテストケースでテストして反例が見つからなかった場合、ギブアップして [`sorry`](./Sorry.md) と同様にはたらきます。-/

/--
warning: Gave up after failing to generate values that fulfill the preconditions 100 times.
---
warning: declaration uses 'sorry'
-/
#guard_msgs (warning) in
  example (a : Nat) : a ≠ a → a ≤ 1 := by
    plausible

/- ## 引数
引数として、オプションを渡すことができます。

### numInst

`numInst` を設定すると、ギブアップするまでに行うテストの回数を指定することができます。
-/

/--
warning: Gave up after failing to generate values that fulfill the preconditions 10 times.
---
warning: declaration uses 'sorry'
-/
#guard_msgs (warning) in
  example (a : Nat) : a ≠ a → a ≤ 1 := by
    plausible (config := { numInst := 10 })
