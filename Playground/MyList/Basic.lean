import Playground.SeeCmd

/- # List を自前で定義して Append の基本的性質を示す -/

/-- 自前で定義した`List` -/
inductive MyList (α : Type) where
  /-- 空のリスト -/
  | nil
  /-- リストの先頭に要素を追加する -/
  | cons (head : α) (tail : MyList α)
deriving DecidableEq


/-- 空の`MyList` -/
notation:max "m[]" => MyList.nil

#see List.cons
/-- `MyList`に要素を追加する -/
infixr:70 " ::: " => MyList.cons

-- 異なる記法で定義したリストが同じであることのテスト
#guard (3 ::: m[]) = MyList.cons 3 .nil

/-- 自作のリストリテラル構文。なお末尾のカンマは許可される -/
syntax "m[" term,*,? "]" : term

macro_rules
  | `(m[ ]) => `(m[])
  | `(m[$x]) => `($x ::: m[])
  | `(m[$x, $xs,*]) => `($x ::: (m[$xs,*]))

-- 構文のテスト
#guard m[1, 2, 3] = 1 ::: 2 ::: 3 ::: m[]
#guard m[1, ] = 1 ::: m[]
#guard m[] = MyList.nil (α := Unit)
