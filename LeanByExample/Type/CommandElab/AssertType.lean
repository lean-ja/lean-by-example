import Lean

open Lean Elab Command Term

-- メタ変数を表示しない
set_option pp.mvars false

/-- 与えられた項の型をチェックするコマンド -/
syntax (name := assertType) "#assert_type " term " : " term : command

@[command_elab assertType]
def evalAssertType : CommandElab := fun stx => do
  match stx with
  | `(command| #assert_type $termStx : $typeStx) =>
    liftTermElabM
      try
        let type ← elabType typeStx
        let _ ← elabTermEnsuringType termStx type
        logInfo "success"
      catch | _ => throwError "failure"
  | _ => throwUnsupportedSyntax

/-⋆-//-- info: success -/
#guard_msgs in --#
#assert_type 5 : Nat

/-⋆-//-- info: success -/
#guard_msgs in --#
#assert_type 42 : ?_

/-⋆-//--
error: Type mismatch
  [1, 2, 3]
has type
  List ?_
but is expected to have type
  Nat
-/
#guard_msgs (error) in --#
#assert_type [1, 2, 3] : Nat
