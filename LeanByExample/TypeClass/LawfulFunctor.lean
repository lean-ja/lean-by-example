/- # LawfulFunctor

`LawfulFunctor` は、[`Functor`](./Functor.md) 型クラスにファンクタ則を満たすという条件を加えたものです。

ファンクタ則とは、ファンクタ `F : Type u → Type u` が満たしているべきルールで、以下のようなものです。

1. `Functor.map` は恒等関数を保存する。つまり `id <$> x = x` が成り立つ。
2. `Functor.map` は関数合成を保存する。つまり `(f ∘ g) <$> x = f <$> (g <$> x)` が成り立つ。

`LawfulFunctor` クラスは、これをほぼそのままコードに落とし込んだものとして、おおむね次のように定義されています。（実際の定義には `map_const` というフィールドがありますが、ここでは省略しました）
-/
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

universe u v

variable {α β γ : Type u}

class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  /-- 恒等関数を保つ -/
  id_map (x : f α) : id <$> x = x

  /-- 合成を保つ -/
  comp_map (g : α → β) (h : β → γ) (x : f α) : (h ∘ g) <$> x = h <$> g <$> x

end Hidden --#
