/- # Tactic

`Lean.Elab.Tactic.Tactic` 型の項は、タクティクの内部実装を表現しています。タクティクとは証明の状態を操作する関数であり、`Tactic` 型は `Syntax → TacticM Unit` という関数型そのものです。
-/
import Lean
import Qq --#
import Batteries.Tactic.Exact --#

open Lean Elab Tactic in

example : Tactic = (Syntax → TacticM Unit) := by rfl

/- ## Tactic 型からタクティクを作る

`Tactic` 型の項からはタクティクを定義することができます。

### trivial タクティクの制限版

[`trivial`](#{root}/Tactic/Trivial.md) タクティクの機能を制限し、`True` というゴールを閉じる機能だけを持つタクティクを構成することができます。[^trivial]
-/

syntax (name := myTrivial) "my_trivial" : tactic

open Lean Elab Tactic Qq in

@[tactic myTrivial]
def evalMyTrivial : Tactic := fun _stx => do
  -- 現在のゴールを取得する
  let goal : MVarId ← getMainGoal
  try
    -- ゴールが `True.intro` で閉じられるか試す
    goal.assignIfDefEq q(True.intro)
  catch _error =>
    -- 失敗した場合はゴールの型を取得してエラーメッセージを表示する
    let goalType ← goal.getType
    throwError "my_trivialタクティクが失敗しました。ゴールの型は`{goalType}`であって`True`ではありません。"

example : True := by
  my_trivial

/-⋆-//-- error: my_trivialタクティクが失敗しました。ゴールの型は`False`であって`True`ではありません。 -/
#guard_msgs in --#
example : False := by
  my_trivial

/- ### assumption タクティク

`assumption` タクティクのように、ゴールの証明が既に仮定にあるときにゴールを閉じるタクティクは次のように `Tactic` 型の関数によって実装できます。
-/

syntax (name := myAssumption) "my_assumption" : tactic

open Lean Elab Tactic in

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

/- [^trivial]: このコード例を書くにあたり [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide) を参考にしました。-/
