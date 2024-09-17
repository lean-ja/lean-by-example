/- # match_pattern

`match_pattern` 属性を付与すると、元々コンストラクタしか使用できない `match` 式でのパターンマッチの枝に、指定した関数を使うことができるようになります。
-/

/-- 自前で定義したリスト -/
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

variable {α : Type}

/-- MyList の `cons` コンストラクタに対するラッパー。中身は同じ -/
def MyList.myCons (a : α) (as : MyList α) : MyList α :=
  MyList.cons a as

-- 最初は `match` の中で `MyList.myCons` を使うことはできない
/-- error: invalid pattern, constructor or constant marked with '[match_pattern]' expected -/
#guard_msgs in
  def badLength : MyList α → Nat
    | MyList.nil => 0
    | MyList.myCons _ as => 1 + badLength as

-- `match_pattern` 属性を付与する
attribute [match_pattern] MyList.myCons

-- これで `match` の中で `MyList.myCons` を使うことができる
def goodLength : MyList α → Nat
  | MyList.nil => 0
  | MyList.myCons _ as => 1 + goodLength as
