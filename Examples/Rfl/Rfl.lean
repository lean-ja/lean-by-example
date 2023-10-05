import Mathlib.Tactic.Relation.Rfl

-- `n ≤ n` を示すために必要
import Mathlib.Data.Nat.Basic

-- ANCHOR: first
inductive MyEq {α : Type u} : α → α → Prop
  | refl (a : α) : MyEq a a

attribute [refl] MyEq.refl

example (n : ℕ) : MyEq n n := by rfl
-- ANCHOR_END: first

-- ANCHOR: nat
-- `import Mathlib.Data.Nat.Basic` が必要
example (n : Nat) : n ≤ n := by rfl
-- ANCHOR_END: nat
