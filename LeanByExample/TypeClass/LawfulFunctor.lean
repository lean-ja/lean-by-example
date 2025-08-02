import Aesop --#
/- # LawfulFunctor

`LawfulFunctor` は、[`Functor`](./Functor.md) 型クラスに関手則を満たすという条件を加えたものです。

関手則とは、関手 `F : Type u → Type u` が満たしているべきルールで、以下のようなものです。

1. `Functor.map` は恒等関数を保存する。つまり `id <$> x = x` が成り立つ。
2. `Functor.map` は関数合成を保存する。つまり `(f ∘ g) <$> x = f <$> (g <$> x)` が成り立つ。

型が合っているだけでは「`Functor.map` とは、関手というコンテナに包まれた内部の値に関数を適用するもの」という意味論が成り立たないことがあります。関手則は、この意味論が正当になるための条件を与えます。

`LawfulFunctor` クラスは、関手則をほぼそのままコードに落とし込んだものとして、おおむね次のように定義されています。
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

関手則の帰結を紹介しましょう。

### 関手は型の同値性を保つ

まず、型 `A, B` は全単射 `f : A → B` とその逆射 `g : B → A` が存在するとき **同値(equivalent)** であるといい、これを `(· ≃ ·)` で表します。つまり `A ≃ B` であるとは、`f : A → B` と `g : B → A` が存在して `f ∘ g = id` かつ `g ∘ f = id` が成り立つことを意味します。

関手則が守られているとき、関手 `F` は合成を保ち、かつ `id` を `id` に写すので、関手は同値性を保つことになります。

{{#include ./LawfulFunctor/MapEquiv.md}}

### 関手は Unit との図式を保つ

型と関数がなす圏 `Type` を考えると、ここでは `Unit` が終対象になっています。つまり、任意の型 `A : Type` に対して、`A → Unit` という関数が一意的に存在します。（関数外延性は仮定します）この多相的な関数を仮に `unit : (A : Type) → A → Unit` と書くことにします。

ここで、任意の関数 `f : A → B` に対して、`A` と `B` のそれぞれから `Unit` への関数が一意的に存在するので、`(unit B) ∘ f = unit A` が成り立ちます。

関手則を満たしている関手 `F : Type → Type` があったとしましょう。このとき `F` は関数合成を保つので、`F` によって誘導される関数も同じ等式を満たします。表記を簡単にするために `(f <$> ⬝)` のことを `f*` と書くことにすると、`(unit B)* ∘ f* = (unit A)*` が成り立ちます。

(だから何だという感じがするかもしれませんが、`(unit ·)*` という多相的な関数によって `map` の実装が非常に限定されているということです。)
-/

/- ## 関手の例

いくつか `LawfulFunctor` クラスのインスタンスを作ってみます。-/

/- ### Id

`Id` は関手則を満たします。
-/

def MyId (α : Type) := α

def MyId.map {α β : Type} (f : α → β) (x : MyId α) : MyId β := f x

instance : Functor MyId where
  map := MyId.map

instance : LawfulFunctor MyId where
  map_const := by intros; rfl
  id_map := by intros; rfl
  comp_map := by intros; rfl

/- ### List

[`List`](#{root}/Type/List.md) は関手則を満たします。
-/

/-- 自前で定義したリスト -/
inductive MyList (α : Type) where
  | nil
  | cons (head : α) (tail : MyList α)

notation:80 "[]" => MyList.nil
infixr:80 "::" => MyList.cons

/-- リストの中身に関数をそれぞれ適用する -/
def MyList.map {α β : Type} (f : α → β) (xs : MyList α) : MyList β :=
  match xs with
  | [] => []
  | x :: xs => f x :: MyList.map f xs

instance : Functor MyList where
  map := MyList.map

instance : LawfulFunctor MyList where
  map_const := by intros; rfl
  id_map := by
    intro α xs
    dsimp [(· <$> ·)]
    induction xs with grind [MyList.map]
  comp_map := by
    intro α β γ g h xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      dsimp [(· <$> ·), MyList.map] at ih ⊢
      rw [ih]

/- ### Option

[`Option`](#{root}/Type/Option.md) は関手則を満たします。
-/
@[aesop unsafe 70% cases]
inductive MyOption (α : Type) where
  | none
  | some (x : α)

def MyOption.map {α β : Type} (f : α → β) (x : MyOption α) : MyOption β :=
  match x with
  | none => none
  | some x => some (f x)

instance : Functor MyOption where
  map := MyOption.map

instance : LawfulFunctor MyOption where
  map_const := by intros; rfl
  id_map := by aesop
  comp_map := by aesop

/- ### (A → ·)

`fun X => (A → X)` という対応 `Type → Type` は関手則を満たします。
-/

/-- 型から、その型への関数型を返す -/
abbrev Hom (A : Type) (X : Type) := A → X

instance {A : Type} : Functor (Hom A) where
  map f g := f ∘ g

instance {A : Type} : LawfulFunctor (Hom A) where
  map_const := by aesop
  id_map := by aesop
  comp_map := by aesop
