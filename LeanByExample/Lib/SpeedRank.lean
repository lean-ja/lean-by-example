import Lean.Elab.Command

open Lean Elab Command in

/-- 2つのコマンドのうち最初のコマンドのほうが `n` 倍早く終わることを確かめるコマンド -/
elab "#speed_rank " "(" "ratio" ":=" n:num ")" "|" stx1:command "|" stx2:command : command => do
  let start_time ← IO.monoMsNow
  elabCommand stx1
  let end_time ← IO.monoMsNow
  let time1 := end_time - start_time

  let start_time ← IO.monoMsNow
  elabCommand stx2
  let end_time ← IO.monoMsNow
  let time2 := end_time - start_time

  logInfo m!"1つめのコマンドの実行時間: {time1}ms"
  logInfo m!"2つめのコマンドの実行時間: {time2}ms"

  let threshold := n.getNat
  unless time1 * threshold < time2 do
    throwError m!"エラー: 1つめのコマンドが期待されるより速くありません。"
