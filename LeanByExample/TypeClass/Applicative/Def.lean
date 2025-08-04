--#--
/--
info: class Applicative.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
number of parameters: 1
parents:
  Applicative.toFunctor : Functor f
  Applicative.toPure : Pure f
  Applicative.toSeq : Seq f
  Applicative.toSeqLeft : SeqLeft f
  Applicative.toSeqRight : SeqRight f
fields:
  Functor.map : {α β : Type u} → (α → β) → f α → f β :=
    fun {α β} x y => pure x <*> y
  Functor.mapConst : {α β : Type u} → α → f β → f α :=
    fun {α β} => Functor.map ∘ Function.const β
  Pure.pure : {α : Type u} → α → f α
  Seq.seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
  SeqLeft.seqLeft : {α β : Type u} → f α → (Unit → f β) → f α :=
    fun {α β} a b => Function.const β <$> a <*> b ()
  SeqRight.seqRight : {α β : Type u} → f α → (Unit → f β) → f β :=
    fun {α β} a b => Function.const α id <$> a <*> b ()
constructor:
  Applicative.mk.{u, v} {f : Type u → Type v} [toFunctor : Functor f] [toPure : Pure f] [toSeq : Seq f]
    [toSeqLeft : SeqLeft f] [toSeqRight : SeqRight f] : Applicative f
field notation resolution order:
  Applicative, Functor, Pure, Seq, SeqLeft, SeqRight
-/
#guard_msgs in #print Applicative
--#--
namespace Hidden --#

class Applicative.{u, v} (f : Type u → Type v) extends Functor f where
  /-- `a : α` が与えられたとき、`pure a : f α` は「何もせずに `a` を返すアクション」を表す。 -/
  pure {α : Type u} : α → f α

  /--
  `<*>` 演算子の実装。
  モナドにおいては、`mf <*> mx` は `do let f ← mf; x ← mx; pure (f x)` と同じになる。
  つまり、まず関数を評価し、次に引数を評価して適用する。
  予期しない順序で評価されることを避けるために、`mx` は `Unit → f α` という関数を使って遅延的に取得される。
  -/
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

  map := fun x y => seq (pure x) (fun _ => y) -- デフォルト実装

end Hidden --#
