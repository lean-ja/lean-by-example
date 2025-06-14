/- # choose

`h : ∀ x, ∃ y, P(x, y)` が成り立っているときに、`choose f hf using h` は関数 `f : X → Y` と `f` が満たす性質 `hf : ∀ x, P(x, f x)` のペアを作ります。
-/
import Mathlib.Tactic.Choose

section
  -- X,Y は型で P : X → Y → Prop は述語
  variable (X Y : Type) (P : X → Y → Prop)

  theorem choice (h : ∀ x, ∃ y, P x y) : ∃ f : X → Y, ∀ x, P x (f x) := by
    -- 関数 `f : X → Y` を構成する
    choose f hf using h

    exact ⟨f, hf⟩
end
/- ## 舞台裏
`choose` は裏で選択原理 [`Classical.choice`](#{root}/Declarative/Axiom.md#ClassicalChoice) を使用しています。
-/

/-⋆-//-- info: 'choice' depends on axioms: [Classical.choice] -/
#guard_msgs in --#
#print axioms choice

/- `choose` が自動で示してくれることを選択原理 `Classical.choice` を使って手動で示すこともできます。例えば以下のようになります。
-/
section
  /- ## choose タクティクを使わずに同等のことをする例 -/

  variable (X Y : Type) (P : X → Y → Prop)

  example (h : ∀ x, ∃ y, P x y) : ∃ f : X → Y, ∀ x, P x (f x) := by
    -- `f` を作る
    let f' : (x : X) → {y // P x y} := by
      intro x
      have hne_st : Nonempty {y // P x y} := by
        let ⟨y, py⟩ := h x
        exact ⟨⟨y, py⟩⟩
      exact Classical.choice hne_st

    let f : X → Y := fun x ↦ (f' x).val

    -- 上記で作った関数が条件を満たすことを示す
    have h₁ : ∀ x, P x (f x) := by
      intro x
      exact (f' x).property

    exists f

end
