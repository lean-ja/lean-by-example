
/-- パーサ

* 返り値が `Option` で包まれているのは、パースが成功するとは限らないため
* 返り値の `α × String` は、`α` がパース結果、`String` が残りの入力文字列を表す
-/
def Parser (α : Type) := String → Option (α × String)

/-- 基礎的なパーサ

入力文字が空の時は失敗し、それ以外の時は最初の文字を消費して返す
*MEMO*: `String` に対してちょっと変わったパターンマッチをする例になっている
-/
def Parser.item : Parser Char := fun input =>
  match input with
  | ⟨[]⟩ => none
  | ⟨x :: xs⟩ => some (x, ⟨xs⟩)

open Parser

#guard item "abc" = some ('a', "bc")
