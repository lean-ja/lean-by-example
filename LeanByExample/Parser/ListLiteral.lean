/- # リストリテラル

`[x₁, x₂, .. , xₙ]` は、[List α](#{root}/Type/List.md) の項を簡単に作るための構文です。

もしこの構文がなければ、`List α` の項を作るためにはコンストラクタを使用するしかないので、次のように書く必要があります。
-/

/-- 自前で定義したリスト型 -/
inductive MyList (α : Type) where
  | nil
  | cons (head : α) (tail : MyList α)
deriving DecidableEq

notation:max " [] " => MyList.nil
infixr:80 " :: " => MyList.cons

-- 項を作るのが面倒
/-⋆-//-- info: 1 :: 2 :: 3 :: [] : MyList Nat -/
#guard_msgs in --#
#check 1 :: 2 :: 3 :: []

/- しかし、リストリテラル構文があるおかげで、次のように見やすく簡潔に書くことができます。 -/

/-- 自作のリストリテラル構文。なお末尾のカンマは許可される -/
syntax "my[" term,*,? "]" : term

macro_rules
  | `(my[]) => `([])
  | `(my[$x]) => `($x :: [])
  | `(my[$x, $xs,*]) => `($x :: (my[$xs,*]))

-- 項を作るのが楽になった！
#check my[1, 2, 3]

-- 末尾のコンマは無視される
#check my[1, 2, 3, ]

-- リストリテラル構文のテスト
#guard
  let actual := my[1, 2, 3]
  let expected := 1 :: 2 :: 3 :: []
  actual = expected
