/-- パーサ

* 返り値が `Option` で包まれているのは、パースが成功するとは限らないため
* 返り値の `α × String` は、`α` がパース結果、`String` が残りの入力文字列を表す
-/
def Parser (α : Type) := String → Option (α × String)

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

instance : Monad Parser where
  bind := fun {_α _β} p f input =>
    match p input with
    | none => none
    | some (v, out) => f v out

/-- 基礎的なパーサ

入力文字が空の時は失敗し、それ以外の時は最初の文字を消費して返す
*MEMO*: `String` に対してちょっと変わったパターンマッチをする例になっている
-/
def Parser.item : Parser Char := fun input =>
  match input with
  | ⟨[]⟩ => none
  | ⟨x :: xs⟩ => some (x, ⟨xs⟩)

/-- 3文字の文字列にマッチするパーサー -/
def Parser.three : Parser String := do
  let x ← item
  let y ← item
  let z ← item
  return String.mk [x, y, z]

#guard Parser.three "abcdef" = some ("abc", "def")
