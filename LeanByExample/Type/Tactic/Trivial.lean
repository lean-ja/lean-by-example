import Qq
import Batteries

/-- True というゴールを閉じる機能だけを持つタクティク -/
syntax (name := myTrivial) "my_trivial" : tactic

open Lean Elab Tactic Qq

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
