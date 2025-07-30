import Lean

open Lean Elab Command PrettyPrinter Delaborator

def delabForCheckExp (c : Name) : Delab := delabForallParamsWithSignature fun binders type => do
  let binders := binders.filter fun binder => binder.raw.isOfKind ``Parser.Term.explicitBinder
  return ⟨← `(declSigWithId| $(mkIdent c) $binders* : $type)⟩

elab tk:"#check_exp " name:ident : command => runTermElabM fun _ => do
  for c in (← realizeGlobalConstWithInfos name) do
    addCompletionInfo <| .id name name.getId (danglingDot := false) {} none
    let info ← getConstInfo c
    logInfoAt tk <| .ofFormatWithInfosM (ppExprWithInfos (delab := delabForCheckExp c) info.type)

#check_exp id
-- id (a : α) : α

#check id
