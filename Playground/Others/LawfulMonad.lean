variable {m : Type → Type} [Monad m]
variable {A B C : Type}

/-- モナドに包まれたアクションの合成 -/
def kleisliComp (f : A → m B) (g : B → m C) : A → m C := fun a => do
  let b ← f a
  g b

set_option pp.notation false in

-- `bind`が使用されているのが見える
#print kleisliComp

infix:60 " ∘K " => kleisliComp

@[defeq, simp]
theorem kleisliComp_def (f : A → m B) (g : B → m C) : f ∘K g = fun a => f a >>= g := by
  rfl

variable [LawfulMonad m]
variable {D : Type} (h : C → m D)
variable (f : A → m B) (g : B → m C)

/-- kleisliComp において、pure を左から合成しても変わらない -/
@[simp, grind]
theorem pure_comp : (pure ∘K f) = f := by
  funext x
  dsimp
  exact pure_bind x f

/-- kleisliComp において、pure を右から合成しても変わらない -/
theorem comp_pure : (f ∘K pure) = f := by
  funext x
  dsimp
  exact bind_pure (f x)

/-- kleisliComp による合成は、結合的である -/
theorem comp_assoc : (f ∘K g) ∘K h = f ∘K (g ∘K h) := by
  funext x
  dsimp
  exact bind_assoc (f x) g h
