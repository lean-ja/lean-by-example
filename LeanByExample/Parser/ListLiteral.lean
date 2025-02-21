/- # リストリテラル

-/

inductive MyList (α : Type) where
  | nil
  | cons (head : α) (tail : MyList α)

-- 項を作るのが面倒
#check MyList.cons 2 MyList.nil

/-- 自作のリストリテラル構文。なお末尾のカンマは許可される -/
syntax "my[" term,*,? "]" : term

macro_rules
  | `(my[]) => `(MyList.nil)
  | `(my[$x]) => `(MyList.cons $x MyList.nil)
  | `(my[$x, $xs,*]) => `(MyList.cons $x (my[$xs,*]))

-- 項を作るのが楽になった！
#check my[1, 2, 3]
