import Batteries

syntax (name := myAssumption) "my_assumption" : tactic

open Lean Elab Tactic

@[tactic myAssumption]
def evalMyAssumption : Tactic := fun _stx => withMainContext do
  -- 現在のゴールとローカルコンテキストを取得する
  let goal ← getMainGoal
  let ctx ← getLCtx

  for (decl : LocalDecl) in ctx do
    -- ローカル宣言の種類がデフォルトでない場合はスキップする
    if decl.kind != .default then
      continue
    try
      -- ゴールにローカル宣言の変数を代入する
      goal.assignIfDefEq decl.toExpr
      -- 成功したら終了
      return
    catch _ =>
      -- 失敗しても無視して次の候補に進む
      pure ()
  throwError "my_assumptionタクティクが失敗しました。"

example {P : Prop} (hP : P) : P := by
  my_assumption

/-⋆-//-- error: my_assumptionタクティクが失敗しました。 -/
#guard_msgs in --#
example {P Q : Prop} (hP : P) : Q := by
  my_assumption
