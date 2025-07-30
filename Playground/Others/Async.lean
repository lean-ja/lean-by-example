import Std.Internal.Async.Basic

open Std.Internal.IO.Async

def expensiveOperation (n : Nat) : Async Nat := do
  IO.sleep 1000
  return n

def manyInParallel (n : Nat) : Async Nat := do
  let tasks := (Array.range n).map expensiveOperation
  let results ← concurrentlyAll tasks
  return results.sum

-- Only runs about a second
#time #eval (manyInParallel 11).wait
