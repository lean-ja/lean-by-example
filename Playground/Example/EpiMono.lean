namespace Function

variable {A B : Type}

/-- 関数の単射性 -/
def Injective (f : A → B) : Prop :=
  ∀ (x y : A), f x = f y → x = y

/-- 関数の全射性 -/
def Surjective (f : A → B) : Prop :=
  ∀ y : B, ∃ x : A, f x = y

variable {C : Type}
variable {f : B → C} {g : A → B}

theorem surj_of_comp_surj (h : Surjective (f ∘ g)) : Surjective f := by
  dsimp [Surjective] at *
  -- 実は try? で解決できる
  intro c
  have ⟨a, ha⟩ := h c
  grind

theorem inj_of_comp_inj (h : Injective (f ∘ g)) : Injective g := by
  dsimp [Injective] at *
  -- 実は try? で解決できる
  intro a₁ a₂ g_eq
  replace h := h a₁ a₂
  grind

/-- モノ射 -/
def mono (f : A → B) : Prop :=
  ∀ C : Type, ∀ g₁ g₂ : C → A, f ∘ g₁ = f ∘ g₂ → g₁ = g₂

/-- 単射ならばモノ射 -/
theorem mono_of_inj {f : A → B} (h : Injective f) : mono f := by
  intro C g₁ g₂ g_eq
  dsimp [Injective] at h
  ext c
  have eq : f (g₁ c) = f (g₂ c) := calc
    _ = (f ∘ g₁) c := rfl
    _ = (f ∘ g₂) c := by rw [g_eq]
    _ = f (g₂ c) := rfl
  replace h := h (g₁ c) (g₂ c) eq
  assumption

/-- モノ射ならば単射 -/
theorem inj_of_mono {f : A → B} (h : mono f) : Injective f := by
  intro a₁ a₂ f_eq
  dsimp [mono] at h

  let C := Fin 2
  let g₁ : C → A := fun _ => a₁
  let g₂ : C → A := fun _ => a₂
  replace h := h C g₁ g₂

  have : f ∘ g₁ = f ∘ g₂ := by grind
  replace h := h this

  have : a₁ = a₂ := calc
    _ = g₁ 0 := rfl
    _ = g₂ 0 := by rw [h]
    _ = a₂ := rfl
  assumption

/-- エピ射 -/
def epi (f : A → B) := ∀ C : Type, ∀ g₁ g₂ : B → C, g₁ ∘ f = g₂ ∘ f → g₁ = g₂

/-- 全射ならばエピ射 -/
theorem epi_of_surj {f : A → B} (h : Surjective f) : epi f := by
  intro C g₁ g₂ g_eq
  dsimp [Surjective] at h
  ext b
  obtain ⟨a, ha⟩ := h b
  rw [← ha]

  -- ここで`grind`が成功しないのマジ？
  fail_if_success grind

  have : g₁ (f a) = g₂ (f a) := calc
    _ = (g₁ ∘ f) a := rfl
    _ = (g₂ ∘ f) a := by rw [g_eq]
    _ = g₂ (f a) := rfl
  assumption

end Function
