
import Lean
import Qq

open Lean Meta Elab Command Qq

private def failGenerically (e : Expr) : TermElabM Unit := do
  throwError "Expression{indentExpr e}\ndid not evaluate to `true`"

private def fail (e : Expr) : TermElabM Unit := do
  let_expr Decidable.decide p _ := e | failGenerically e
  let_expr Eq _ lhs rhs := p | failGenerically e
  let lhs_fmt_expr : Q(Format) ← mkAppM ``repr #[lhs]
  let rhs_fmt_expr : Q(Format) ← mkAppM ``repr #[rhs]
  let lhs_fmt ← unsafe evalExpr Format q(Format) lhs_fmt_expr
  let rhs_fmt ← unsafe evalExpr Format q(Format) rhs_fmt_expr
  throwError
    "Expression{indentExpr e}\n\
    did not evaluate to `true`\n\
    ---\n\
    {lhs} = {lhs_fmt} but {rhs} = {rhs_fmt}"

/-- 等式を評価して不成立だったときに、左辺と右辺の値を表示するような
`#guard` コマンドの派生コマンド -/
elab "#guard_diff" e:term : command => liftTermElabM do
  let e ← Term.elabTermEnsuringType e q(Bool)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let mvars ← getMVars e
  if mvars.isEmpty then
    let v ← unsafe evalExpr Bool q(Bool) e
    unless v do fail e
  else
    _ ← Term.logUnassignedUsingErrorInfos mvars

/-⋆-//--
error: Expression
  decide (3 * 4 = 2 + 2)
did not evaluate to `true`
---
3 * 4 = 12 but 2 + 2 = 4
-/
#guard_msgs in --#
#guard_diff 3 * 4 = 2 + 2
