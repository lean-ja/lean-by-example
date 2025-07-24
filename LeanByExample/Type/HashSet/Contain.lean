import Lean

open Std

/-- 長さ `n` で、中身の値が 0 以上 `bound` 以下であるようなリストをランダム生成する -/
def randList (n : Nat) (bound : Nat) : IO (List Nat) := do
  let mut out := []
  for _ in [0 : n] do
    let x ← IO.rand 0 bound
    out := x :: out
  return out

/-- 実験に使用するリスト・HashSet のサイズ -/
private def sampleSize := 1000_000

/-- 実験に使用するための巨大なリストをランダム生成する -/
private def genSampleList : IO (List Nat) := do
  let size := sampleSize
  let lst ← randList size (size * 1000)
  return lst

/-- 実験に使用するための巨大な HashSet をランダム生成する -/
private def genSampleHashSet : IO (HashSet Nat) := do
  let lst ← genSampleList
  return HashSet.ofList lst

/-- 試す回数 -/
private def trial_time := 100

/-- リストが`contain`を実行するのにかかる平均時間 -/
@[noinline]
def listContainAvgTime : IO Nat := do
  let lst ← genSampleList
  let mut total_time := 0
  let mut useless := false -- 実行時に最適化されないように、無駄な計算をする
  for i in [sampleSize : sampleSize + trial_time] do
    let start_time ← IO.monoNanosNow
    let b := lst.contains i
    let end_time ← IO.monoNanosNow
    useless := !useless && b -- 無駄な計算をする
    let elapsed := end_time - start_time
    total_time := total_time + elapsed
  return total_time / trial_time

/-- ハッシュセットが`contains`を実行するのにかかる平均時間 -/
@[noinline]
def hashSetContainAvgTime : IO Nat := do
  let s ← genSampleHashSet
  let mut total_time := 0
  let mut useless := false -- 実行時に最適化されないように、無駄な計算をする
  for i in [sampleSize : sampleSize + trial_time] do
    let start_time ← IO.monoNanosNow
    let b := s.contains i
    let end_time ← IO.monoNanosNow
    useless := !useless && b -- 無駄な計算をする
    let elapsed := end_time - start_time
    total_time := total_time + elapsed
  return total_time / trial_time

def main : IO Unit := do
  let list_avg_time ← listContainAvgTime
  IO.println s!"Average time for list.contains: {list_avg_time} ns"

  let hash_avg_time ← hashSetContainAvgTime
  IO.println s!"Average time for hashSet.contains: {hash_avg_time} ns"

  if list_avg_time < hash_avg_time then
    throw <| .userError s!"List is faster: {list_avg_time} ns < {hash_avg_time} ns"

#eval main
