import Lean.Compiler.CSimpAttr
import Lean.Elab.Command

open Lean Elab Command

/-- 与えられた定理が `[csimp]` 属性を持っているかどうかをチェックするコマンド -/
elab "#check_csimp " id:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  if Compiler.hasCSimpAttribute (← getEnv) declName then
    logInfo m!"{.ofConstName declName} has the [csimp] attribute"
  else
    logInfo m!"{.ofConstName declName} does not have the [csimp] attribute"

namespace CheckCsimpExample

def slow (n : Nat) : Nat := n

def fast (n : Nat) : Nat := n

@[csimp]
theorem slow_eq_fast : @slow = @fast := rfl

/-- info: slow_eq_fast has the [csimp] attribute -/
#guard_msgs in --#
#check_csimp slow_eq_fast

theorem zero_eq_zero : 0 = 0 := rfl

/-- info: zero_eq_zero does not have the [csimp] attribute -/
#guard_msgs in --#
#check_csimp zero_eq_zero

end CheckCsimpExample
