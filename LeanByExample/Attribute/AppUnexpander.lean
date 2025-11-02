/- # app_unexpander
`[app_unexpander]` 属性を `Unexpander` 型の関数に付与すると、[`#check`](#{root}/Diagnostic/Check.md) コマンドおよびinfoviewでの表示のされ方を変更することができます。

一般に、`[app_unexpander c]` 属性を `Unexpander` 型の関数に付与することで、`c` の（関数適用の）表示を変更することができます。
-/

/-- 人に挨拶をする関数 -/
def greet (x : String) := s!"Hello, {x}!"

set_option linter.unusedVariables false --#

open Lean PrettyPrinter in

/-- すべての挨拶の表示を強制的に hello world に変えてしまう -/
@[app_unexpander greet]
def unexpGreet : Unexpander := fun stx =>
  match stx with
  | `(greet $x) => `("hello world")
  | _ => throw ()

-- #check の表示が上書きされて変わる
/-⋆-//-- info: "hello world" : String -/
#guard_msgs in --#
#check greet "Alice"

-- infoview における表示も変わってしまう
/-⋆-//--
trace: s : String
h : s = "hello world"
⊢ String
-/
#guard_msgs in --#
example (s : String) (h : s = greet "Alice" ) : String := by
  trace_state

  exact "hello"

-- #eval の表示は変わらない
/-⋆-//-- info: "Hello, Alice!" -/
#guard_msgs in --#
#eval greet "Alice"

/- ## 使用例

### 集合の内包表記
[`macro_rules`](#{root}/Declarative/MacroRules.md) コマンドで定義した集合の内包記法の表示のされ方を制御する例を挙げます。 -/

/-- α を全体集合として、その部分集合の全体。
α の部分集合と α 上の述語を同一視していることに注意。 -/
def Set (α : Type) := α → Prop

/-- 述語 `p : α → Prop` に対応する集合 -/
def setOf {α : Type} (p : α → Prop) : Set α := p


-- ## 集合の内包表記

/-- 内包表記 `{ x : α | p x }` の `x : α` の部分のための構文。
`: α` の部分はあってもなくてもよいので `( )?` で囲っている。-/
syntax extBinder := ident (" : " term)?

/-- 内包表記 `{ x : α | p x }` の `{ | }` の部分のための構文。 -/
syntax (name := setBuilder) "{" extBinder " | " term "}" : term

/-- 内包表記の意味をマクロとして定義する -/
macro_rules
  | `({ $x:ident : $type | $p }) => `(setOf (fun ($x : $type) => $p))
  | `({ $x:ident | $p }) => `(setOf (fun ($x : _) => $p))

-- 内包表記が使えるようになったが、#check コマンドの出力では
-- いま定義した記法が使われないという問題がある
/-⋆-//-- info: setOf fun n => ∃ m, n = 2 * m : Set Nat -/
#guard_msgs in --#
#check {n : Nat | ∃ m, n = 2 * m}


open Lean PrettyPrinter in

/-- #check コマンドの出力でも内包表記を使用するようにする -/
@[app_unexpander setOf]
def setOf.unexpander : Unexpander := fun stx =>
  match stx with
  | `($_ fun $x:ident => $p) => `({ $x:ident | $p })
  | `($_ fun ($x:ident : $ty:term) => $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()


-- ## app_unexpander のテスト

/-⋆-//-- info: {n | ∃ m, n = 2 * m} : Set Nat -/
#guard_msgs in --#
#check {n | ∃ m, n = 2 * m}

/-⋆-//-- info: {n | ∃ m, n = 2 * m} : Set Nat -/
#guard_msgs in --#
#check {n : Nat | ∃ m, n = 2 * m}

/- ### リストリテラル

`List` 型の項を作る構文である、[リストリテラル](#{root}/Syntax/ListLiteral.md)を自作して、リストリテラルの表示を調整する例を挙げます。
-/

/-- 自前で定義した`List` -/
inductive MyList (α : Type) where
  /-- 空のリスト -/
  | nil
  /-- リストの先頭に要素を追加する -/
  | cons (head : α) (tail : MyList α)
deriving DecidableEq

/-- 空の`MyList` -/
notation:max "⟦⟧" => MyList.nil

/-- `MyList`に要素を追加する -/
infixr:70 " ::: " => MyList.cons

/-- 自作のリストリテラル構文。なお末尾のカンマは許可される -/
syntax "⟦" term,*,? "⟧" : term

macro_rules
  | `(⟦ ⟧) => `(⟦⟧)
  | `(⟦ $x ⟧) => `($x ::: ⟦⟧)
  | `(⟦ $x, $xs,* ⟧) => `($x ::: (⟦ $xs,* ⟧))

-- 構文は正しく動作しているが、`#check` コマンドの出力に構文が反映されていない
/-⋆-//-- info: 1 ::: 2 ::: 3 ::: ⟦⟧ : MyList Nat -/
#guard_msgs in --#
#check ⟦1, 2, 3⟧

namespace MyList

  open Lean PrettyPrinter

  @[app_unexpander MyList.cons]
  def unexpandCons : Unexpander := fun stx =>
    match stx with
    | `($(_) $head $tail) =>
      match tail with
      | `(⟦⟧) => `(⟦ $head ⟧)
      | `(⟦ $xs,* ⟧) => `(⟦ $head, $xs,* ⟧)
      | `(⋯) => `(⟦ $head, $tail ⟧)
      | _ => throw ()
    | _ => throw ()

  /-⋆-//-- info: ⟦1, 2, 3⟧ : MyList Nat -/
  #guard_msgs in --#
  #check ⟦1, 2, 3⟧

  /-⋆-//-- info: ⟦1⟧ : MyList Nat -/
  #guard_msgs in --#
  #check ⟦1, ⟧

end MyList
