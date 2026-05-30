import Lean

syntax (name := tada) "tada" : tactic

open Lean Elab Tactic Term

@[tactic tada]
def evalTada : Tactic := fun _stx => do
  -- 現在の未解決のゴールを取得する
  let goals ← getUnsolvedGoals

  -- 未解決のゴールがある場合
  unless goals.isEmpty do
    reportUnsolvedGoals goals
    throwAbortCommand

  logInfo "🎉 おめでとうございます！証明完了です！"

/-- info: 🎉 おめでとうございます！証明完了です！ -/
#guard_msgs in --#
example : True := by
  trivial
  tada
