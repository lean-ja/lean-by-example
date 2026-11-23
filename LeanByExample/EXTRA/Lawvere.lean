/- # Lawvere の不動点定理

Cantor の対角線論法の一般化として、関数型への全射または関数型からの単射があるとき、不動点コンビネータが作れるという定理が証明できます。
これを Lawvere の不動点定理と呼びます。

> **定理**: Lawvere の不動点定理
>
> 型 `A, X : Type` に対して関数 `r : A → (A → X)` と `s : (A → X) → A` が存在し、`r ∘ s = id` を満たすとする。
> このとき任意の関数 `f : X → X` は不動点を持つ。
-/

variable {A X : Type}
variable (r : A → (A → X)) (s : (A → X) → A)

/-- 不動点コンビネータ。
任意の関数 f : X → X に対してその不動点を返す -/
def fixPoint : (X → X) → X := fun f =>
  -- 対角評価関数
  let Δ : A → X := fun a => r a a
  Δ (s (f ∘ Δ))

theorem fixPoint_spec (h : r ∘ s = id) (f : X → X) :
    (fixPoint r s) f = f (fixPoint r s f) := by
  let Y := fixPoint r s
  let Δ : A → X := fun a => r a a

  have : Y f = f (Y f) := calc
    _ = Δ (s (f ∘ Δ)) := by rfl -- Y の定義から
    _ = r (s (f ∘ Δ)) (s (f ∘ Δ)) := by rfl -- Δ の定義から
    _ = (r ∘ s) (f ∘ Δ) (s (f ∘ Δ)) := by rfl
    _ = (f ∘ Δ) (s (f ∘ Δ)) := by rw [h]; simp -- 仮定から
    _ = f (Y f) := by rfl -- Y の定義から
  assumption

/-- Lawvere の不動点定理 -/
theorem lawvere_fixpoint (h : r ∘ s = id) :
    ∀ f : X → X, ∃ u : X, f u = u := by
  -- 関数 f が与えられたとする。
  intro (f : X → X)

  exists fixPoint r s f
  rw [← fixPoint_spec r s h f]
