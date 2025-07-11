import Playground.MyList.C02Syntax

/- # MyList の ToString と Repr インスタンスを作る -/

/- ## ToString -/

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

/- ## Repr -/

open Lean

instance : Repr (MyList α) where
  reprPrec l _ := toString l

#guard reprStr ⟦1, 2, 3⟧ = "⟦1, 2, 3⟧"
