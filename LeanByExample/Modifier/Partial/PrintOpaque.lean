import Batteries.Tactic.PrintOpaques

/-- 無限ループする関数 -/
partial def endless {α : Type u} (a : α) : α :=
  endless a

def exampleFunc (a : Nat) : Nat :=
  endless a + 1

/-- info: 'exampleFunc' depends on opaque or partial definitions: [endless] -/
#guard_msgs in --#
#print opaques exampleFunc
