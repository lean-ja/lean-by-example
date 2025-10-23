/- # Async

`Std.Internal.IO.Async.Async` は、（まだ実験的な機能で正式リリースされていない機能ですが）非同期計算をサポートします。ここで非同期計算とは、複数の計算を「他の計算の結果を待たずに」実行するようなものを指します。
-/
import Std.Internal.Async.Basic
import Lean

open Std.Internal.IO.Async Async

/-- 疑似的に重い処理を非同期で行う関数 -/
def expensiveOperationAsync (n : Nat) : Async Nat := do
  IO.sleep 100  -- 100 ミリ秒スリープ
  return n

/-- 疑似的に重い処理を同期で行う関数 -/
def expensiveOperationSync (n : Nat) : IO Nat := do
  IO.sleep 100  -- 100 ミリ秒スリープ
  return n

/-- `n` 回、非同期に重い処理を並列実行し、その結果の合計を返す -/
def manyInParallel (n : Nat) : Async Nat := do
  -- `expensiveOperationAsync` を n 個生成
  let tasks := (Array.range n).map expensiveOperationAsync
  -- すべての非同期タスクを並列に実行し、結果を集める
  let results ← concurrentlyAll tasks
  return results.sum

/-- `n` 回、同期に重い処理を順次実行し、その結果の合計を返す -/
def manyInSync (n : Nat) : IO Nat := do
  -- `expensiveOperationSync` を n 個生成
  let tasks := (Array.range n).map expensiveOperationSync
  -- 順次に全て実行して結果を集める
  let results ← tasks.mapM id
  return results.sum


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

-- 非同期版の方が速い
#speed_rank (ratio := 1)
  | #eval (manyInParallel 3).wait
  | #eval manyInSync 3
