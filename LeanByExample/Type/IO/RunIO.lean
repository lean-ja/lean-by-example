import Lean

open Lean Meta Elab Term

def toExprIO {α : Type} [ToExpr α] (x : IO α) : IO Expr :=
  toExpr <$> x

elab tk:"run_io " t:doSeq : term <= expectedType => withRef t do
  let expectedType := mkApp (mkConst ``IO) expectedType
  let v ← elabTermEnsuringType (← `(do $t)) expectedType
  synthesizeSyntheticMVarsNoPostponing
  let v ← instantiateMVars v
  if (← logUnassignedUsingErrorInfos (← getMVars v)) then
    throwAbortTerm
  let v ← mkAppM ``toExprIO #[v]
  let io ← unsafe evalExpr (IO Expr) (mkApp (mkConst ``IO) (mkConst ``Expr)) v
  let (out, x) ← IO.FS.withIsolatedStreams io.toBaseIO
  unless out.isEmpty do
    logInfoAt tk out
  match x with
  | .ok x => return x
  | .error e => throwErrorAt tk e.toString

-- 使用例。ランダムな数を選んでいるのに、型を `Nat` にすることができる
def number : Nat := run_io IO.rand 0 1000

-- 実行前に既に値が決定されているため、
-- 平気で証明ができる
example : 0 ≤ number ∧ number < 1001 := by
  simp [number.eq_def]
