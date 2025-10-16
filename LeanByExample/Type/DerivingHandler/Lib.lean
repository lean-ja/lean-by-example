import Lean
import LeanByExample.Type.DerivingHandler.ToUnit

open Lean Elab Command

/-- `ToUnit` のためのインスタンス自動導出関数 -/
def deriveToUnitInstance (declNames : Array Name) : CommandElabM Bool := do
  for declName in declNames do
    let term := mkCIdent declName
    let cmd ← `(command| instance : ToUnit $term := ⟨fun _ => ()⟩)
    elabCommand cmd
  return true

initialize
  registerDerivingHandler ``ToUnit deriveToUnitInstance
