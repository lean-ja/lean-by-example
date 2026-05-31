import Lean.Elab.Command

open Lean Elab Command in

/-- コマンドが１秒以内に終了することを確かめる -/
elab "#in_second " stx:command : command => do
  let start_time ← IO.monoMsNow
  elabCommand stx
  let end_time ← IO.monoMsNow
  let time := end_time - start_time
  if time ≤ 1000 then
    logInfo m!"time: {time}ms"
  else
    throwError m!"It took more than one second for the command to run."

#in_second #eval 1 + 1
