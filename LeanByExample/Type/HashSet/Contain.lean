import Lean

open Std

/-- HashSetとListで処理を共通化するための型クラス -/
class DS (col : Type) (α : Type) where
  /-- 要素があるか判定する -/
  contains : col → α → Bool

  /-- ランダムな要素を生成する -/
  gen : IO col

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

instance : DS (List Nat) Nat where
  contains := fun lst => lst.contains
  gen := genSampleList

instance : DS (HashSet Nat) Nat where
  contains := fun s x => s.contains x
  gen := genSampleHashSet

/-- 試す回数 -/
private def trial_time := 100

/-- `contain`を実行するのにかかる平均時間 -/
@[noinline]
def containAvgTime (type : Type) [inst : DS type Nat] : IO Nat := do
  let col ← inst.gen
  let mut total_time := 0
  let mut useless := false -- 実行時に最適化されないように、無駄な計算をする
  for i in [sampleSize : sampleSize + trial_time] do
    let start_time ← IO.monoNanosNow
    let b := inst.contains col i
    let end_time ← IO.monoNanosNow
    useless := !useless && b -- 無駄な計算をする
    let elapsed := end_time - start_time
    total_time := total_time + elapsed
  return total_time / trial_time

def main : IO Unit := do
  let list_avg_time ← containAvgTime (type := List Nat)
  IO.println s!"Average time for list.contains: {list_avg_time} ns"

  let hash_avg_time ← containAvgTime (type := HashSet Nat)
  IO.println s!"Average time for hashSet.contains: {hash_avg_time} ns"

  if list_avg_time < hash_avg_time then
    throw <| .userError s!"List is faster: {list_avg_time} ns < {hash_avg_time} ns"

#eval main
