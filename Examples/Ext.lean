import Aesop -- `aesop` タクティクを使うために必要
import Mathlib.Data.SetLike.Basic -- `ext` タクティクで集合の等号を展開するために必要
import Std.Tactic.Ext -- `ext` タクティクを使うために必要

variable {α : Type}

-- `s` と `t` は `α` の部分集合
variable (s t : Set α)

/-! ## ext -/

example : s ∩ t = t ∩ s := by
  -- `x ∈ α` を取る．
  ext x

  -- ` x ∈ s ∩ t ↔ x ∈ t ∩ s` を証明すればよい
  show x ∈ s ∩ t ↔ x ∈ t ∩ s

  aesop

/-!
  ## A ⊆ B

  `A ⊆ B` を示すために元を取る操作は `intro` でできる．
-/

example : (s ∩ t) ⊆ t := by
  -- `ext` は使えない
  try ext x

  intro x hx

  simp_all
