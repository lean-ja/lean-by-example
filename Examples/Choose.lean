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


-- ANCHOR: no_choose
variable (P : X → Y → Prop)

noncomputable example (h : ∀ x, ∃ y, P x y) : ∃ f : X → Y, ∀ x, P x (f x) := by
  -- `f` を作る
  let f' : (x : X) → {y // P x y} := fun x ↦
    have hne_st : Nonempty {y // P x y} :=
      let ⟨y, py⟩ := h x; ⟨⟨y, py⟩⟩
    Classical.choice hne_st

  let f : X → Y := fun x ↦ (f' x).val

  -- 上記で作った関数が条件を満たすことを示す
  have h₁ : ∀ x, P x (f x) := by
    intro x
    exact (f' x).property

  exists f
-- ANCHOR_END: no_choose