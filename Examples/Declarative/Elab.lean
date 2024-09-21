/- # elab

[`🏷️メタプログラミング`](./?search=🏷メタプログラミング)

`elab` コマンドは、構文に意味を与えるためのコマンドです。特定の構文の解釈を、手続きとして記述するときに使用されます。

以下の例は、証明が終了したときに 🎉 でお祝いしてくれるタクティクを自作する例です。[^zulip]
-/
import Lean

open Lean Elab Tactic Term

elab "tada" : tactic => do
  -- 未解決のゴールを List として取得する
  let gs ← getUnsolvedGoals

  -- ゴールが空なら 🎉 でお祝いする
  if gs.isEmpty then
    logInfo "Goals accomplished 🎉"
  else
    -- ゴールが残っているというメッセージを出す
    reportUnsolvedGoals gs

    -- エラーにする
    throwAbortTactic

/--
error: unsolved goals
⊢ True
-/
#guard_msgs in
  example : True := by tada

/-- info: Goals accomplished 🎉 -/
#guard_msgs in
  example : True := by
    trivial
    tada

/- [^zulip]: Zulip のスレッド [new members > lean3 or 4?](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Lean.203.20or.204.3F) からコード例を引用しています。-/
