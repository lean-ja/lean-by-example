import Playground.MyList.Basic

variable {α : Type} [ToString α]

protected def MyList.toString (l : MyList α) : String :=
  match l with
  | m[] => "m[]"
  | head ::: tail => s!"m[{head}, {aux tail}]"
where
  aux (l : MyList α) : String :=
    match l with
    | m[] => ""
    | head ::: m[] => s!"{head}"
    | head ::: tail => s!"{head}, {aux tail}"

/-- `MyList`を文字列に変換できるようにする -/
instance : ToString (MyList α) where
  toString := MyList.toString

#guard toString m[1, 2, 3] = "m[1, 2, 3]"

open Lean

instance : Repr (MyList α) where
  reprPrec l _ := toString l

#eval m[1, 2, 3]

-- `#check`の出力はまだ見づらい形のまま
-- これはデラボレータがないから
#check m[1, 2, 3]
