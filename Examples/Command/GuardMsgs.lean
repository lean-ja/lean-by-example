/-
# guard_msgs

`#guard_msgs` コマンドは，あるコマンドの出力が与えられた文字列と一致するか検証します．
-/
import Mathlib.Algebra.Group.Defs -- 逆数を使うために必要 --#
import Std.Tactic.GuardMsgs -- guard_msgs コマンドを使うために必要

/-- info: 2 -/
#guard_msgs in
#eval 2

/-- error: failed to synthesize instance
  HAdd ℕ String String -/
#guard_msgs in
#eval (2 + "hello" : String)

/-!
`#guard_msgs` コマンドは空白の数に敏感で，空白の長さによって通ったり通らなかったりします．
次の例では，`instance` と `Inv α` の間に不自然に空白がありますが，この長さの空白でないとエラーになります．
-/

variable (α : Type)

/--
error: failed to synthesize instance   Inv α
-/
#guard_msgs in
#check (_ : α)⁻¹

#print Inv
