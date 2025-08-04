variable {α : Type} [Add α] [Zero α] [Inhabited α]

@[noinline]
def sum! (xs : Array α) : α := Id.run do
  let mut acc : α := 0
  for i in [0:xs.size] do
    acc := acc + xs[i]!
  return acc

@[noinline]
def sum (xs : Array α) : α := Id.run do
  let mut acc : α := 0
  for h : i in [0:xs.size] do
    acc := acc + xs[i]
  return acc

@[noinline]
def main : IO Unit := do
  let size := 10_000_000
  let array := Array.range size

  let start_time1 ← IO.monoNanosNow
  let result1 := sum! array
  let end_time1 ← IO.monoNanosNow
  let time1 := end_time1 - start_time1
  IO.println s!"sum! result: {result1}, time taken: {time1} ns"

  let start_time2 ← IO.monoNanosNow
  let result2 := sum array
  let end_time2 ← IO.monoNanosNow
  let time2 := end_time2 - start_time2
  IO.println s!"sum result: {result2}, time taken: {time2} ns"

  if time1 < time2 then
    throw <| .userError s!"sum! is faster: {time1} ns < {time2} ns"

#eval main
