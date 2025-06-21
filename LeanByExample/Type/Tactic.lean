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

例として [`trivial`](#{root}/Tactic/Trivial.md) タクティクの機能を制限し、`True` というゴールを閉じる機能だけを持つタクティクを構成してみます。[^trivial]
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

/- [^trivial]: このコード例を書くにあたり [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide) を参考にしました。-/
