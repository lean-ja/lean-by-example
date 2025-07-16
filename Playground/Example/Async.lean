import Std.Internal.Async.Basic

open Std.Internal.IO.Async

def expensiveOperation (n : Nat) : Async Nat := do
  IO.sleep 1000
  return 2 * n

def manyInParallel (n : Nat) : Async Nat := do
  let tasks := (Array.range n).map expensiveOperation
  let results ← concurrentlyAll tasks
  return results.sum

-- Only runs about a second
#eval (manyInParallel 10).wait
