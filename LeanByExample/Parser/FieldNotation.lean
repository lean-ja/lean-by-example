/- # フィールド記法

**フィールド記法(field notation)** とは、大雑把に言えば `T` が `e` の型であるときに、関数適用 `T.f e` を `e.f` と書き表せるという記法のことです。あたかも `f` が `e` のフィールドであるかのように見えるのでこの名前があります。

典型的な例は、[構造体](#{root}/Declarative/Structure.md) `S` の項 `e : S` に対して、構造体のフィールドのアクセサ関数 `S.f` の適用を `e.f` と書けることです。
-/
import Lean --#

/-- 平面 -/
structure Point (α : Type) where
  x : α
  y : α

-- `Point` のフィールドへのアクセサ関数
#check Point.x
#check Point.y

-- フィールド記法を使ってアクセスすることができる
#guard
  let p : Point Nat := { x := 1, y := 2 }
  p.x = Point.x p

/- ここで `S` は構造体である必要はなく、任意の型で構いません。すなわち任意の型 `S` とその項 `e : S` に対して、`e.f` は `S.f (p := e)` と解釈されます。ただし、ここで `p` は関数 `S.f` の型 `S` を持つような最初の明示的引数です。 -/

/-- 例示のための意味のない帰納型 -/
inductive S where
  | fst (n : Nat)
  | snd (s : String) (n : Nat)

/-- `_x : Unit` という余計な引数を持つ関数 -/
def S.toNat (_x : Unit) (s : S) : Nat :=
  match s with
  | S.fst n => n
  | S.snd _ n => n

#guard
  let e : S := S.fst 42

  -- フィールド記法が使える
  e.toNat () = 42

/- ## 関数型に対して

`e` が関数であるとき、`e.f` は `Function.f (p := e)` に翻訳されます。ただし、ここで `p` は関数 `Function.f` の、関数型を持つような最初の明示的引数です。
-/
section
  variable {α β γ : Type}

  /-- 関数の単射性 -/
  def Function.injective (f : α → β) : Prop := ∀ {x y}, f x = f y → x = y

  example (f : α → β) (g : β → γ) : (g ∘ f).injective → f.injective := by
    -- `g ∘ f` が単射だと仮定する。
    intro h

    -- このとき `f` は単射である。
    exact show f.injective from by
      -- なぜなら、仮に `f x = f y` とすると
      intro x y hg

      -- `(g ∘ f) x = (g ∘ f) y` が成り立っており
      have : (g ∘ f) x = (g ∘ f) y := by simp [hg]

      -- `g ∘ f` が単射であることから `x = y` が導かれるため。
      exact h this

end
/- ## パラメータを取る型に対して

`e` が `T ...` の項であり、かつ関数 `T.f` が存在するとき、`e.f` は `T.f (p := e)` に翻訳されます。ただし、ここで `p` は関数 `T.f` の型 `T ...` を持つような最初の明示的引数です。
-/

/-- リストの最小値をそのインデックスと共に出力する -/
def List.minIdx? {α : Type} [LE α] [DecidableLE α] (xs : List α) : Option (Nat × α) :=
  loop xs 0
where
  loop : List α → Nat → Option (Nat × α)
  | [], _ => none
  | x :: xs, i =>
    match loop xs (i + 1) with
    | none => some (i, x)
    | some (j, y) =>
      if x ≤ y then (i, x) else some (j, y)

-- フィールド記法が使用できている
#guard
  let e := [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
  e.minIdx? = some (1, 1)

/- ## 詳細な仕様
詳細な仕様は、パーサのドキュメントコメントに書かれています。 -/

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name ← liftCoreM do realizeGlobalConstNoOverload x
  if let some s ← findDocString? (← getEnv) name then
  logInfo m!"{s}"

/-⋆-//--
info: The *extended field notation* `e.f` is roughly short for `T.f e` where `T` is the type of `e`.
More precisely,
* if `e` is of a function type, `e.f` is translated to `Function.f (p := e)`
  where `p` is the first explicit parameter of function type
* if `e` is of a named type `T ...` and there is a declaration `T.f` (possibly from `export`),
  `e.f` is translated to `T.f (p := e)` where `p` is the first explicit parameter of type `T ...`
* otherwise, if `e` is of a structure type,
  the above is repeated for every base type of the structure.

The field index notation `e.i`, where `i` is a positive number,
is short for accessing the `i`-th field (1-indexed) of `e` if it is of a structure type.
-/
#guard_msgs in --#
#doc Lean.Parser.Term.proj

/- ## 制約

フィールド記法の制約として、フィールド記法を使用すると型強制が通らなくなります。
-/

/-- 標準のリストのラッパー -/
structure MyList (α : Type) where
  data : List α

/-- `MyList` から `List` への型強制 -/
instance {α : Type} : Coe (MyList α) (List α) where
  coe l := l.data

-- 型強制がはたらくので本来 List が来るべきところに MyList が来ていても通る
#check
  let l : MyList Nat := { data := [1, 2, 3] }
  List.foldl (· + ·) 0 l

-- フィールド記法だと型強制がはたらかない
#check_failure
  let l : MyList Nat := { data := [1, 2, 3] }
  l.foldl (· + ·) 0
