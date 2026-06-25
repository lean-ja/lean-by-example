import LeanByExample.EXTRA.EnumToString.MkToStringInst --#

open Lean Elab Command

private def mkToStringInstForEnumHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty then
    throwError "型が指定されていません"

  for declName in declNames do
    let cmd ← liftTermElabM <| mkToStringInstForEnum declName
    elabCommand cmd
  return true

initialize
  registerDerivingHandler ``ToString mkToStringInstForEnumHandler
