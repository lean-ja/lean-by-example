--#--
/--
info: class LawfulApplicative.{u, v} (f : Type u → Type v) [Applicative f] : Prop
number of parameters: 2
parents:
  LawfulApplicative.toLawfulFunctor : LawfulFunctor f
fields:
  LawfulFunctor.map_const : ∀ {α β : Type u}, Functor.mapConst = Functor.map ∘ Function.const β
  LawfulFunctor.id_map : ∀ {α : Type u} (x : f α), id <$> x = x
  LawfulFunctor.comp_map : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x :=
    ⋯
  LawfulApplicative.seqLeft_eq : ∀ {α β : Type u} (x : f α) (y : f β), x <* y = Function.const β <$> x <*> y
  LawfulApplicative.seqRight_eq : ∀ {α β : Type u} (x : f α) (y : f β), x *> y = Function.const α id <$> x <*> y
  LawfulApplicative.pure_seq : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x
  LawfulApplicative.map_pure : ∀ {α β : Type u} (g : α → β) (x : α), g <$> pure x = pure (g x)
  LawfulApplicative.seq_pure : ∀ {α β : Type u} (g : f (α → β)) (x : α), g <*> pure x = (fun h => h x) <$> g
  LawfulApplicative.seq_assoc : ∀ {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)),
      h <*> (g <*> x) = Function.comp <$> h <*> g <*> x
constructor:
  LawfulApplicative.mk.{u, v} {f : Type u → Type v} [Applicative f] [toLawfulFunctor : LawfulFunctor f]
    (seqLeft_eq : ∀ {α β : Type u} (x : f α) (y : f β), x <* y = Function.const β <$> x <*> y)
    (seqRight_eq : ∀ {α β : Type u} (x : f α) (y : f β), x *> y = Function.const α id <$> x <*> y)
    (pure_seq : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x)
    (map_pure : ∀ {α β : Type u} (g : α → β) (x : α), g <$> pure x = pure (g x))
    (seq_pure : ∀ {α β : Type u} (g : f (α → β)) (x : α), g <*> pure x = (fun h => h x) <$> g)
    (seq_assoc :
      ∀ {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)), h <*> (g <*> x) = Function.comp <$> h <*> g <*> x) :
    LawfulApplicative f
field notation resolution order:
  LawfulApplicative, LawfulFunctor
-/
#guard_msgs in
#print LawfulApplicative
--#--
namespace Hidden --#

variable {α β γ : Type}

/-- アプリカティブ則 -/
class LawfulApplicative (f : Type → Type) [Applicative f] : Prop extends LawfulFunctor f where
  /-- `pure` が `seq` の直前にくる場合、その部分はただの `Functor.map` と同じになる -/
  pure_seq (g : α → β) (x : f α) : pure g <*> x = g <$> x

  /-- `pure` の結果に関数を `map` することは、その関数を `pure` の内部で適用することと同じ。 -/
  map_pure (g : α → β) (x : α) : g <$> (pure x : f α) = pure (g x)

  /-- `seq` の後に `pure` を使うことは、`Functor.map` と同じになる。 -/
  seq_pure (g : f (α → β)) (x : α) : g <*> pure x = (fun h => h x) <$> g

  /--
  `seq` は結合的である。

  計算の順序を保ったまま `seq` 呼び出しの入れ子構造を変えても、同値な計算になる。
  これは、`seq` が単に順序付け以上のことはしていないことを意味する。
  -/
  seq_assoc (x : f α) (g : f (α → β)) (h : f (β → γ)) : h <*> (g <*> x) = ((@Function.comp α β γ) <$> h) <*> g <*> x

end Hidden --#
