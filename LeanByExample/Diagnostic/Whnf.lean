/- # \#whnf
`#whnf` は、式を弱頭正規形(weak head normal form)に簡約するコマンドです。

弱頭正規形とは、式の構成要素の最初の部分(head)がそれ以上簡約できない形になっている状態のことです。たとえば式の頭が[帰納型](#{root}/Declarative/Inductive.md)のコンストラクタや、ラムダ式になっていれば弱頭正規形です。
-/
import Mathlib.Tactic.Conv -- `#whnf` コマンドを使うために必要

-- 弱頭正規形
/-- info: (fun x => x + 1) 1 :: List.map (fun x => x + 1) [2, 3] -/
#guard_msgs in #whnf [1, 2, 3].map (· + 1)

-- 弱頭正規形で止まらずに完全に簡約した場合
/-- info: [2, 3, 4] -/
#guard_msgs in #reduce [1, 2, 3].map (· + 1)

-- 上記の式がなぜ弱頭正規形であるのかの説明
example : [1, 2, 3].map (· + 1) = [2, 3, 4] := calc
  -- フィールド記法を展開する
  _ = List.map (· + 1) [1, 2, 3] := by rfl

  -- ラムダ式に展開される
  _ = List.map (fun x => x + 1) [1, 2, 3] := by rfl

  -- List.map を使うために、引数をコンストラクタに分解する
  _ = List.map (fun x => x + 1) (1 :: [2, 3]) := by rfl

  -- List.map の定義を展開する
  _ = (fun x => x + 1) 1 :: List.map (fun x => x + 1) [2, 3] := by rfl

  -- これはコンストラクタが先頭に来ているので、弱頭正規形になっている
  _ = List.cons ((fun x => x + 1) 1) (List.map (fun x => x + 1) [2, 3]) := by rfl

  _ = [2, 3, 4] := by rfl

/- ## 型クラスの実装を調べる
一見して使いどころがないようですが、型クラスの実装を調べたいときに有用です。

たとえば、以下のように `Many` という型を定義し、`Monad` 型クラスの実装を与えたとします。
-/

/-- 遅延評価版の List もどき -/
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

variable {α β : Type}

def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union {α : Type} : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)

/-- Many にモナドの実装を与える -/
instance instMonadMany : Monad Many where
  pure := Many.one
  bind := Many.bind

/- `Monad` 型クラスは [`Functor`](#{root}/TypeClass/Functor.md) クラスや `Applicative` クラスの実装を含むので、`Many` は `Functor` や `Applicative` のインスタンスでもあります。このインスタンスは次のように `inferInstance` という関数で構成することができますが、その中身を `#print` で出力してみても実装がわかりません。-/

def instManyFunctor : Functor Many := inferInstance

/--
info: def instManyFunctor : Functor Many :=
inferInstance
-/
#guard_msgs in #print instManyFunctor

/- しかし、`#whnf` コマンドに渡すと実装内容を表示してくれます。-/

-- Functor の実装を表示させることができた
/--
info: { map := fun {α β} f x => x.bind (Many.one ∘ f),
  mapConst := fun {α β} => (fun f x => x.bind (Many.one ∘ f)) ∘ Function.const β }
-/
#guard_msgs in #whnf (inferInstance : Functor Many)

-- Applicative については、実装を得るためには下位クラスを使う必要がある
/-- info: Applicative.mk -/
#guard_msgs in #whnf (inferInstance : Applicative Many)

-- seq の実装を表示させることができた
/-- info: { seq := fun {α β} f x => f.bind fun y => (x ()).bind (Many.one ∘ y) } -/
#guard_msgs in #whnf (inferInstance : Seq Many)

/- なお、これを `#reduce` で行おうとすると簡約しすぎて読みづらい表示が出てきます。-/

/--
info: {
  map := fun {α β} f x =>
    (Many.rec ⟨fun x => Many.none, PUnit.unit⟩
          (fun a a_1 a_ih =>
            ⟨fun x =>
              (Many.rec ⟨fun x => x, PUnit.unit⟩
                    (fun a a_2 a_ih =>
                      ⟨fun x => Many.more a fun x_1 => (a_ih PUnit.unit).1 x, fun a => (a_ih a).1, fun a => (a_ih a).2⟩)
                    (x a)).1
                ((a_ih PUnit.unit).1 x),
              fun a => (a_ih a).1, fun a => (a_ih a).2⟩)
          x).1
      fun x => Many.more (f x) fun x => Many.none,
  mapConst := fun {α β} x x_1 =>
    (Many.rec ⟨fun x => Many.none, PUnit.unit⟩
          (fun a a_1 a_ih =>
            ⟨fun x =>
              (Many.rec ⟨fun x => x, PUnit.unit⟩
                    (fun a a_2 a_ih =>
                      ⟨fun x => Many.more a fun x_2 => (a_ih PUnit.unit).1 x, fun a => (a_ih a).1, fun a => (a_ih a).2⟩)
                    (x a)).1
                ((a_ih PUnit.unit).1 x),
              fun a => (a_ih a).1, fun a => (a_ih a).2⟩)
          x_1).1
      fun x_2 => Many.more x fun x => Many.none }
-/
#guard_msgs in #reduce (inferInstance : Functor Many)
