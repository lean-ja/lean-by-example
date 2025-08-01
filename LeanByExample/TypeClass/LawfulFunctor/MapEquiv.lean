import Mathlib.Logic.Equiv.Defs

variable {A B : Type} {F : Type → Type}

example [Functor F] [LawfulFunctor F] (h : A ≃ B) : F A ≃ F B := by
  obtain ⟨f, g, hf, hg⟩ := h

  -- 関手 `F` による像で同値になる
  refine ⟨Functor.map f, Functor.map g, ?hFf, ?hFg⟩

  -- infoviewを見やすくする
  all_goals
    dsimp [Function.RightInverse] at *
    dsimp [Function.LeftInverse] at *

  case hFf =>
    have gfid : g ∘ f = id := by
      ext x
      simp_all

    intro x
    have : g <$> f <$> x = x := calc
      _ = (g ∘ f) <$> x := by rw [LawfulFunctor.comp_map]
      _ = id <$> x := by rw [gfid]
      _ = x := by rw [LawfulFunctor.id_map]
    assumption

  case hFg =>
    have fgid : f ∘ g = id := by
      ext x
      simp_all

    intro x
    have : f <$> g <$> x = x := calc
      _ = (f ∘ g) <$> x := by rw [LawfulFunctor.comp_map]
      _ = id <$> x := by rw [fgid]
      _ = x := by rw [LawfulFunctor.id_map]
    assumption
