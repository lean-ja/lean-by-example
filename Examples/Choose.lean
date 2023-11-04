import Mathlib.Tactic.Choose

variable (X Y : Type) (P : X → Y → Prop)

/-! ## choose -/

theorem choice (h : ∀ x, ∃ y, P x y) : ∃ f : X → Y, ∀ x, P x (f x) := by
  -- 写像 `f : X → Y` を構成する
  choose f hf using h

  exact ⟨f, hf⟩

/-!
  ## 選択公理

  `choose` は選択公理を使用します．
  これは `#print axioms` で確認できます．
-/

/- 'choice' depends on axioms: [Classical.choice] -/
#print axioms choice

/-!
  ## choose なしで示した場合

  choose が自動で示してくれることを選択原理 Classical.choice を使って
  手動で示すと例えば以下のようになります．
-/

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
