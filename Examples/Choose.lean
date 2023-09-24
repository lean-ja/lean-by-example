import Mathlib.Tactic.Choose

variable (X Y : Type)


-- ANCHOR: first
example (f : X → Y) (hf : ∀ y, ∃ x, f x = y) : ∃ g : Y → X, ∀ y, f (g y) = y := by
  -- 写像 `g : Y → X` を構成する
  choose g hg using hf

  -- `g` が満たす条件がローカルコンテキストに追加される
  guard_hyp g: Y → X
  guard_hyp hg: ∀ (y : Y), f (g y) = y

  exact ⟨g, hg⟩
-- ANCHOR_END: first
