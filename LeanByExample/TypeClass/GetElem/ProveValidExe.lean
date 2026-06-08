import LeanByExample.Lib.ThisFile

variable {α : Type} [Add α] [Zero α] [Inhabited α]

-- `IO` で包むことにより最適化されて計測時間がおかしくなることを防いでいる。
-- Lean は非 `IO` 計算の順序を実行時に変える最適化を行う。
@[noinline]
def sum! (xs : Array α) : IO α := do
  let mut acc : α := 0
  for i in [0:xs.size] do
    acc := acc + xs[i]!
  return acc

@[noinline]
def sum (xs : Array α) : IO α := do
  let mut acc : α := 0
  for h : i in [0:xs.size] do
    acc := acc + xs[i]
  return acc

/--
`xs[i]`と`xs[i]!`のどちらが速いかを比較するテスト。
-/
@[noinline]
def main : IO Unit := do
  let size := 10_000_000
  let array := Array.range size

  let start_time1 ← IO.monoMsNow
  let result1 ← sum! array
  let end_time1 ← IO.monoMsNow
  let time1 := end_time1 - start_time1

  let start_time2 ← IO.monoMsNow
  let result2 ← sum array
  let end_time2 ← IO.monoMsNow
  let time2 := end_time2 - start_time2

  if time1 < time2 then
    throw <| .userError s!"sum! is faster: {time1} ms < {time2} ms"
  if result1 ≠ result2 then
    throw <| .userError s!"Results do not match. sum!: {result1}, sum: {result2}"

  IO.println s!"✅ [{this_file%}] テスト成功"
  IO.println s!"   sum! にかかった時間: {time1} ms"
  IO.println s!"   sum にかかった時間: {time2} ms"
