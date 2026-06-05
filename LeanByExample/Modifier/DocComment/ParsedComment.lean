import Lean.Elab.Command

open Lean Elab Command Parser

/--
info: def foo :
    -- ここにコメント
    /- ここにもコメント -/
    True :=
  trivial
-/
#guard_msgs in --#
run_cmd liftTermElabM do
  let s := "def foo : \n\
    -- ここにコメント\n\
    /- ここにもコメント -/\n\
    True := trivial"
  let cmd : Command := ⟨← ofExcept <| runParserCategory (← getEnv) `command s⟩
  logInfo (← PrettyPrinter.ppCommand cmd)
