import Playground.SeeCmd

/- # List を自前で定義して構文も用意する -/

open Lean

/-- 自前で定義した`List` -/
inductive MyList (α : Type) where
  /-- 空のリスト -/
  | nil
  /-- リストの先頭に要素を追加する -/
  | cons (head : α) (tail : MyList α)
deriving DecidableEq

section Notation
  /- ## `MyList`のための `notation` -/

  /-- 空の`MyList` -/
  notation:max "⟦⟧" => MyList.nil

  #see List.cons
  /-- `MyList`に要素を追加する -/
  infixr:70 " ::: " => MyList.cons

  -- 異なる記法で定義したリストが同じであることのテスト
  #guard (3 ::: ⟦⟧) = MyList.cons 3 .nil

end Notation

section Syntax
  /- ## MyList のための構文 -/

  /-- 自作のリストリテラル構文。なお末尾のカンマは許可される -/
  syntax "⟦" term,*,? "⟧" : term

  macro_rules
    | `(⟦ ⟧) => `(⟦⟧)
    | `(⟦$x⟧) => `($x ::: ⟦⟧)
    | `(⟦$x, $xs,*⟧) => `($x ::: (⟦$xs,*⟧))

  -- 構文のテスト
  #guard ⟦1, 2, 3⟧ = 1 ::: 2 ::: 3 ::: ⟦⟧
  #guard ⟦1, ⟧ = 1 ::: ⟦⟧
  #guard ⟦⟧ = MyList.nil (α := Unit)

end Syntax


section ToString
  /- ## MyList の ToString と Repr インスタンスを作る -/

  variable {α : Type} [ToString α]

  protected def MyList.toString (l : MyList α) : String :=
    match l with
    | ⟦⟧ => "⟦⟧"
    | head ::: tail => s!"⟦{head}, {aux tail}⟧"
  where
    aux (l : MyList α) : String :=
      match l with
      | ⟦⟧ => ""
      | head ::: ⟦⟧ => s!"{head}"
      | head ::: tail => s!"{head}, {aux tail}"

  /-- `MyList`を文字列に変換できるようにする -/
  instance : ToString (MyList α) where
    toString := MyList.toString

  #guard toString ⟦1, 2, 3⟧ = "⟦1, 2, 3⟧"

  open Lean

  instance : Repr (MyList α) where
    reprPrec l _ := toString l

  #eval ⟦1, 2, 3⟧

end ToString


namespace MyList
  /- ## MyList のためのデラボレータ -/

  open Lean PrettyPrinter

  @[app_unexpander MyList.nil]
  def unexpandMyListNil : Unexpander := fun stx =>
    match stx with
    | `($(_)) => `(⟦⟧)

  @[app_unexpander MyList.cons]
  def cons.unexpander : Unexpander := fun stx =>
    match stx with
    | `($(_) $head $tail) =>
      match tail with
      | `(⟦⟧) => `(⟦ $head ⟧)
      | `(⟦ $xs,* ⟧) => `(⟦ $head, $xs,* ⟧)
      | `(⋯) => `(⟦ $head, $tail ⟧)
      | _ => throw ()
    | _ => throw ()

  #check (⟦⟧ : MyList Nat)
  #check ⟦1, 2, 3⟧

end MyList
