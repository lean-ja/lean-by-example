import Lean
open Lean

open Elab Command Parser in

-- test `Command`
run_cmd liftTermElabM do
  let s := "theorem ohno : \n\
    -- commented out:\n\
    1 = 1 := trivial"
  let cmd : Command := ⟨← ofExcept <| runParserCategory (← getEnv) `command s⟩
  logInfo (← PrettyPrinter.ppCommand cmd)

-- test `Term`
run_cmd Elab.Command.liftTermElabM do
  let s := "∀ x : ℕ,
    -- commented out:\n\
    x = x"
  let cmd : Term := ⟨← ofExcept <| Parser.runParserCategory (← getEnv) `term s⟩
  logInfo (← PrettyPrinter.ppTerm cmd)
