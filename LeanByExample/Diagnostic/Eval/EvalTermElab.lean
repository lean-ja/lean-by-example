import Mathlib.Tactic.Eval

def bar := 1 + 1

def foo₁ := eval% bar

def foo₂ := bar

/-⋆-//--
info: def foo₁ : Nat :=
2
-/
#guard_msgs in --#
#print foo₁

/-⋆-//--
info: def foo₂ : Nat :=
bar
-/
#guard_msgs in --#
#print foo₂
