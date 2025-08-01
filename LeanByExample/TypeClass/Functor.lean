/- # Functor

`Functor` は圏論における **関手(functor)** という概念からその名がある型クラスで、非常に雑な表現をすると、この型クラスを実装した型は「値を包んでいるコンテナのようなもの」として扱うことができます。特定のデータ構造に「包まれて」いる中の値に対して関数を適用していくという操作を行いたいことがありますが、`Functor` のインスタンスはそれを可能にします。

より詳細には、`F : Type u → Type v` に対して `Functor` はおおむね次のように定義されています。
-/
--#--
/--
info: class Functor.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
number of parameters: 1
fields:
  Functor.map : {α β : Type u} → (α → β) → f α → f β
  Functor.mapConst : {α β : Type u} → α → f β → f α :=
    fun {α β} => Functor.map ∘ Function.const β
constructor:
  Functor.mk.{u, v} {f : Type u → Type v} (map : {α β : Type u} → (α → β) → f α → f β)
    (mapConst : {α β : Type u} → α → f β → f α) : Functor f
-/
#guard_msgs in #print Functor
--#--
namespace Hidden --#

universe u v

/-- 関手 -/
class Functor (F : Type u → Type v) : Type (max (u+1) v) where
  /-- 関数 `f : α → β` を関数 `F α → F β` に変換する -/
  map : {α β : Type u} → (α → β) → F α → F β

  /-- `a : α` に対して、定数関数 `const a : β → α` を関数 `F β → F α` に変換する。
  `map` を使うよりも効率的に実装できることがあるので、上書きできるように用意されている。-/
  mapConst : {α β : Type u} → α → F β → F α := Function.comp map (Function.const _)

end Hidden --#
/- つまり、`Functor` のインスタンスは `map` メソッドが使用できます。これは型からわかるように、関数を関数に写す高階関数で、「普通の関数 `f : α → β`」を「`F` に包まれた関数 `F α → F β`」に持ち上げます。`Functor.map` はよく使われる操作であるため、`<$>` という専用の記法が用意されています。 -/
section --#

-- `F` は Functor であると仮定
variable (F : Type → Type) [Functor F]

-- 関数 `g : α → β` と `x : F α` が与えられたとする
variable {α β : Type} (g : α → β)

-- 高階関数を返す
#check (Functor.map g : F α → F β)

-- `<$>` は `map` と同じ
example (x : F α) : g <$> x = Functor.map g x := rfl

end --#
/- 型が合っているだけでは「包まれている値に対して関数を適用する」という意味論にそぐわない挙動をすることがあるので、関手が満たすべきルールが存在し、それは [`LawfulFunctor`](#{root}/TypeClass/LawfulFunctor.md) というクラスにまとめられています。 -/
/- ## 典型的なインスタンス -/

/- ### Id
`Id : Type u → Type u` は「何もしない」関手です。
-/

/-- `Id` の `Functor.map` の実装を真似て作った関数 -/
def Id.myMap {α β : Type} (f : α → β) (x : Id α) : Id β := f x

/-- `Id` の `Functor.map` は `Id.myMap` のように定義されている -/
example {α β : Type} (f : α → β) (x : Id α) : Id.myMap f x = f <$> x := rfl

/- ### List
`Functor` 型クラスの典型的なインスタンスのひとつが [`List`](#{root}/Type/List.md) です。これにより「リストの各要素に関数を適用する」ための簡単な方法が提供されます。
-/

/-- 標準にある `List.map` の実装を真似て実装した `map` 処理 -/
def List.myMap {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: List.myMap f xs

/-- `List` の `Functor.map` は `List.myMap` のように定義されている -/
example {α β : Type} (f : α → β) (xs : List α) : List.myMap f xs = f <$> xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp_all [List.myMap, Functor.map]

-- リストの各要素を２倍する例
#guard (· * 2) <$> [1, 2, 3, 4, 5] = [2, 4, 6, 8, 10]

/- ### Option
[`Option`](#{root}/Type/Option.md) も `Functor` 型クラスのインスタンスになっています。これにより「`x? : Option` が `some x` の場合にだけ関数を適用し、`none` なら `none` を返す」という操作のための簡単な方法が提供されます。
-/

/-- 標準にある `Option.map` の実装を真似て実装した `map` 処理 -/
def Option.myMap {α β : Type} (f : α → β) : Option α → Option β
  | some x => some (f x)
  | none => none

/-- `Option` の `Functor.map` は `Option.myMap` のように定義されている -/
example {α β : Type} (f : α → β) (x : Option α) : Option.myMap f x = f <$> x := by
  cases x <;> rfl

#guard (· * 2) <$> some 2 = some 4
#guard (· * 2) <$> [1, 2, 3][4]? = none

/-⋆-//-- info: 20 -/
#guard_msgs in --#
#eval (· * 2) <$> (10 : Id Nat)

/- ### (A → ·)
任意の型 `A : Type u` に対して、`fun X => (A → X)` という対応は関手になります。
-/

/-- 型から、その型への関数型を返す -/
abbrev Hom (A : Type) (X : Type) := A → X

/-- 関数合成を map として `Hom A` は関手になる -/
instance {A : Type} : Functor (Hom A) where
  map f g := f ∘ g

#guard
  let doubleLength : Hom String Nat := (· * 2) <$> String.length
  doubleLength "hello" = 10 && doubleLength "world!" = 12

/- 上記で定義した `Hom` は Lean の標準ライブラリでは `ReaderM` と呼ばれます。 -/

/-- 上で定義した Hom は ReaderM に等しい -/
example (A : Type) : ReaderM A = Hom A := rfl

/- ### ((· → A) → A)
任意の型 `A : Type u` に対して、`fun X => (X → A) → A` という対応は関手になります。[^cont]
-/

abbrev Cont (A : Type) (X : Type) := (X → A) → A

instance {A : Type} : Functor (Cont A) where
  map f g := fun h => g (h ∘ f)

/- ### (A × ·)

任意の型 `A : Type` に対して、`A` との直積を取る対応 `fun X => A × X` は関手になります。
-/
section
  -- 最初 Functor インスタンスは用意されていない
  #check_failure (· * 2) <$> ("hello", 20)

  abbrev prodWith (A : Type) (X : Type) := A × X

  local instance {A : Type} : Functor (prodWith A) where
    map f := fun (a, x) => (a, f x)

  #guard (· * 2) <$> ("hello", 20) = ("hello", 40)
end
/- ### (A ⊕ ·)
任意の型 `A : Type` に対して、`A` との直和を取る対応 `fun X => A ⊕ X` は関手になります。
-/
section
  -- 最初 Functor インスタンスは用意されていない
  #check_failure (· * 2) <$> (Sum.inr 20 : String ⊕ Nat)

  abbrev sumWith (A : Type) (X : Type) := Sum A X

  local instance {A : Type} : Functor (sumWith A) where
    map f := fun z =>
      match z with
      | .inl a => Sum.inl a
      | .inr x => Sum.inr (f x)

  #eval (· * 2) <$> (Sum.inr 20 : String ⊕ Nat)
end
/- ## Functor 則

`Functor` 型クラスのインスタンスには満たすべきルールがあります。このルールを破っていても `Functor` 型クラスのインスタンスにすることは可能ですが、避けるべきです。`Functor` 型クラスがルールを満たしていることを証明するためには、[`LawfulFunctor`](#{root}/TypeClass/LawfulFunctor.md) 型クラスを使います。

[^cont]: この関手は、 継続モナド(continuation monad) として知られているものです。詳細は、たとえば [Andrzej Filinski 「Representing monads」(1994)](https://dl.acm.org/doi/10.1145/174675.178047) などを参照のこと。
-/
