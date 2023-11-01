import Aesop
import Mathlib.Data.SetLike.Basic -- `ext` タクティクで集合の等号を展開するために必要
import Mathlib.Tactic.Says
import Std.Tactic.Ext

set_option says.no_verify_in_CI true

variable {α : Type}

-- `s` と `t` は `α` の部分集合
variable (s t : Set α)

/-! ## ext -/

example : s ∩ t = t ∩ s := by
  -- `x ∈ α` を取る．
  ext x

  -- ` x ∈ s ∩ t ↔ x ∈ t ∩ s` を証明すればよい
  show x ∈ s ∩ t ↔ x ∈ t ∩ s

  aesop? says
    simp_all only [Set.mem_inter_iff]
    apply Iff.intro
    · intro a
      simp_all only [and_self]
    · intro a
      simp_all only [and_self]

/-!
  ## A ⊆ B

  `A ⊆ B` を示すために元を取る操作は `intro` でできる．
-/

example : (s ∩ t) ⊆ t := by
  -- `ext` は使えない
  try ext x

  intro x hx

  simp? says
    simp_all only [Set.mem_inter_iff]
