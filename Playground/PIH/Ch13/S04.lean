import Playground.PIH.Ch13.S02

/-- `Parser`の`Functor.map`メソッドの実装

* パーサが成功すれば結果に関数を適用する
* 失敗したら失敗を伝搬する
-/
protected def Parser.map {α β : Type} (f : α → β) (p : Parser α) : Parser β :=
  fun input =>
    match p input with
    | none => none
    | some (a, rest) => some (f a, rest)

instance : Functor Parser where
  map := Parser.map

#guard (Char.toUpper <$> Parser.item) "abc" = some ('A', "bc")

#guard (Char.toUpper <$> Parser.item) "" = none



/-- `Parser`の`Applicative.pure`メソッドの実装 -/
protected def Parser.pure {α : Type} (x : α) : Parser α :=
  fun input => some (x, input)

/-- `Parser`の`Applicative.seq`メソッドの実装

関数を返すパーサ`pg`を、引数を返すパーサ`px ()`に適用して、
「その関数を引数に適用した結果を返すパーサ」を返す
-/
protected def Parser.seq {α β : Type} (pg : Parser (α → β)) (px : Unit → Parser α) : Parser β :=
  fun input =>
    match pg input with
    | none => none
    | some (g, out) => (g <$> px ()) out

instance : Applicative Parser where
  pure := Parser.pure
  seq := Parser.seq

-- `pure`で構成されたパーサは必ずパースに成功する
#guard (pure 1 : Parser Nat) "abc" = some (1, "abc")

open Parser

/-- 3文字を消費し、2つめの文字を捨てて1つめと3つめを返すパーサ -/
def Parser.three : Parser (Char × Char) :=
  pure g <*> item <*> item <*> item
where
  g : Char → Char → Char → Char × Char :=
    fun x _ z => (x, z)

#guard three "abcdef" = some (('a', 'c'), "def")

-- 入力文字列が短すぎる場合は`Applicative`の仕組みにより自動的に失敗する
#guard three "" = none
#guard three "a" = none
#guard three "ab" = none

instance : Monad Parser where
  bind := fun {_α _β} p f input =>
    match p input with
    | none => none
    | some (v, out) => f v out

/-- do構文で定義した Parser.three -/
def Parser.three' : Parser (Char × Char) := do
  let x ← item
  let _ ← item
  let z ← item
  pure (x, z)

#guard Parser.three' "abcdef" = some (('a', 'c'), "def")
