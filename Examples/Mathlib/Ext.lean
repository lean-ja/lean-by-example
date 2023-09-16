import Mathlib.Tactic

-- ANCHOR: first
variable {α : Type}

-- `s` と `t` は `α` の部分集合
variable (s t : Set α)

example : s ∩ t = t ∩ s := by
  -- `x ∈ α` を取る．` x ∈ s ∩ t ↔ x ∈ t ∩ s` を証明すればよい
  ext x

  aesop
-- ANCHOR_END: first