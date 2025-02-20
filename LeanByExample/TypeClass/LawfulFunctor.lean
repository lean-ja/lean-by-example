/- # LawfulFunctor

`LawfulFunctor` は、[`Functor`](./Functor.md) 型クラスに関手則を満たすという条件を加えたものです。

関手則とは、関手 `F : Type u → Type u` が満たしているべきルールで、以下のようなものです。

1. `Functor.map` は恒等関数を保存する。つまり `id <$> x = x` が成り立つ。
2. `Functor.map` は関数合成を保存する。つまり `(f ∘ g) <$> x = f <$> (g <$> x)` が成り立つ。

`LawfulFunctor` クラスは、これをほぼそのままコードに落とし込んだものとして、おおむね次のように定義されています。
-/
import Mathlib.Logic.Equiv.Defs --#
--#--
-- # LawfulFunctor の仕様変更を監視するためのコード
/--
info: class LawfulFunctor.{u, v} (f : Type u → Type v) [Functor f] : Prop
number of parameters: 2
fields:
  LawfulFunctor.map_const : ∀ {α β : Type u}, Functor.mapConst = Functor.map ∘ Function.const β
  LawfulFunctor.id_map : ∀ {α : Type u} (x : f α), id <$> x = x
  LawfulFunctor.comp_map : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x
constructor:
  LawfulFunctor.mk.{u, v} {f : Type u → Type v} [Functor f]
    (map_const : ∀ {α β : Type u}, Functor.mapConst = Functor.map ∘ Function.const β)
    (id_map : ∀ {α : Type u} (x : f α), id <$> x = x)
    (comp_map : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x) : LawfulFunctor f
-/
#guard_msgs in #print LawfulFunctor
--#--

namespace Hidden --#

open Function

universe u v

variable {α β γ : Type u}

class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  /-- `Functor.mapConst` が仕様を満たす -/
  map_const : (Functor.mapConst : α → f β → f α) = Functor.map ∘ const β

  /-- 恒等関数を保つ -/
  id_map (x : f α) : id <$> x = x

  /-- 合成を保つ -/
  comp_map (g : α → β) (h : β → γ) (x : f α) : (h ∘ g) <$> x = h <$> g <$> x

end Hidden --#
/- ## 関手則の帰結

関手則の意味について理解していただくために、関手則の帰結をひとつ紹介します。

まず、型 `A, B` は全単射 `f : A → B` とその逆射 `g : B → A` が存在するとき **同値(equivalent)** であるといい、これを `(· ≃ ·)` で表します。つまり `A ≃ B` であるとは、`f : A → B` と `g : B → A` が存在して `f ∘ g = id` かつ `g ∘ f = id` が成り立つことを意味します。

関手則が守られているとき、関手 `F` は合成を保ち、かつ `id` を `id` に写すので、関手は同値性を保つことになります。
-/
section
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
end
