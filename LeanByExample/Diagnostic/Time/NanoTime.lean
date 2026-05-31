import Lean

open Lean Elab Command Term Meta in

elab "#nano_time " stx:command : command => do
  -- 実行直前に計測開始
  let start_time ← IO.monoNanosNow

  -- コマンドを実行
  elabCommand stx

  -- 実行後に計測終了
  let end_time ← IO.monoNanosNow

  -- 差分を実行時間としてナノ秒単位で出力
  logInfo m!"time: {end_time - start_time}ns"

#nano_time
  #eval 21 * 2
