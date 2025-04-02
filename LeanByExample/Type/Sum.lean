import Mathlib.Logic.Equiv.Defs --#
/- # Sum

`Sum` は、データの選択肢を束ねたものを表現しており、`Sum A B` は `A` と `B` のどちらかの値を取るような型です。`A ⊕ B` と表記されます。
-/
-- `A ⊕ B` と表記される
example {A B : Type} : Sum A B = (A ⊕ B) := by rfl

#check (Sum.inl 42 : Nat ⊕ String)
#check (Sum.inr "hello world" : Nat ⊕ String)

/- 関数 `f : A ⊕ B → C` は、`f₁ : A → C` と `f₂ : B → C` の組に対応するという性質があります。 -/

example {A B C : Type} : (A ⊕ B → C) ≃ (A → C) × (B → C) where
  toFun f := (f ∘ Sum.inl, f ∘ Sum.inr)
  invFun f p := Prod.casesOn f fun f₁ f₂ =>
    match p with
    | Sum.inl a => f₁ a
    | Sum.inr b => f₂ b
  left_inv := by
    intro f
    funext x
    cases x <;> rfl
  right_inv := by
    dsimp [Function.RightInverse, Function.LeftInverse]
    intros
    rfl
