/- # tactic

`[tactic]` 属性は、タクティクの実装である [`Tactic`](#{root}/Type/Tactic.md) 型の関数とタクティクの構文を結び付け、タクティクとして動作するようにします。
-/
import Lean
import Qq
import Batteries.Tactic.Exact

/-- True というゴールだけを閉じる trivial タクティクの制限版 -/
syntax (name := trivialStx) "my_trivial" : tactic

open Lean Elab Tactic Qq in

def trivialImpl : Tactic := fun _stx => do
  -- 現在のゴールを取得する
  let goal : MVarId ← getMainGoal
  try
    -- ゴールが `True.intro` で閉じられるか試す
    goal.assignIfDefEq q(True.intro)
  catch _error =>
    -- 失敗した場合はゴールの型を取得してエラーメッセージを表示する
    let goalType ← goal.getType
    throwError "my_trivialタクティクが失敗しました。ゴールの型は`{goalType}`であって`True`ではありません。"

-- 未実装というエラーになってしまう
/-⋆-//-- error: Tactic `trivialStx` has not been implemented -/
#guard_msgs in --#
example : True := by
  my_trivial

-- [tactic] 属性を使って実装と構文を結びつける
attribute [tactic trivialStx] trivialImpl

-- タクティクとして使えるようになった！
example : True := by
  my_trivial
