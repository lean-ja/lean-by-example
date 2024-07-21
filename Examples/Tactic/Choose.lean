/- # choose

`h : ∀ x, ∃ y, P(x, y)` が成り立っているときに、`choose f hf using h` は写像 `f : X → Y` と `f` が満たす性質 `hf : ∀ x, P(x, f x)` のペアを作ります。
-/
import Mathlib.Tactic.Choose

variable (X Y : Type) (P : X → Y → Prop)

theorem choice (h : ∀ x, ∃ y, P x y) : ∃ f : X → Y, ∀ x, P x (f x) := by
  -- 写像 `f : X → Y` を構成する
  choose f hf using h

  exact ⟨f, hf⟩

/- ## 舞台裏
`choose` は裏で選択原理 [`Classical.choice`](../Command/Declarative/Axiom.md#ClassicalChoice) を使用しています。
-/

/-- info: 'choice' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms choice

/-- info: @Classical.choice : {α : Sort u_1} → Nonempty α → α -/
#guard_msgs in #check @Classical.choice

/- `choose` が自動で示してくれることを選択原理 `Classical.choice` を使って手動で示すこともできます。例えば以下のようになります。
-/

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
