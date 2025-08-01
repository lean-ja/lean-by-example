import Playground.MyList.Basic

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

/-
## MyList のためのデラボレータ
-/

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

/-- info: ⟦⟧ : MyList Nat -/
#guard_msgs in #check (⟦⟧ : MyList Nat)

/-- info: ⟦1, 2, 3⟧ : MyList Nat -/
#guard_msgs in #check ⟦1, 2, 3⟧
