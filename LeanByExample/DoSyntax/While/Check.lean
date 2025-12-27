import LeanByExample.Diagnostic.GuardMsgs.ContainMsg

def searchMinExample (P : Nat → Bool) : Nat := Id.run do
  let mut n := 0
  while !P n do
    n := n + 1
  return n

/-- Lean.Loop.forIn -/
#contain_msg in
  #reduce searchMinExample

/-- info: fun {β} {m} [Monad m] x init f => Lean.Loop.forIn.loop✝ f init -/
#guard_msgs in --#
#reduce @Lean.Loop.forIn
