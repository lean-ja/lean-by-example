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


/-- 空の`MyList` -/
notation:max "⟦⟧" => MyList.nil

#see List.cons
/-- `MyList`に要素を追加する -/
infixr:70 " ::: " => MyList.cons

-- 異なる記法で定義したリストが同じであることのテスト
#guard (3 ::: ⟦⟧) = MyList.cons 3 .nil
