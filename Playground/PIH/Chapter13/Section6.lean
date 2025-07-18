import Playground.PIH.Chapter13.Section5

/-- 述語 `p` を満たす１文字用のパーサ -/
def Parser.sat (p : Char → Bool) : Parser Char := do
  let x ← item
  guard <| p x
  return x

open Parser

#guard sat (fun x => x = 'a') "abc" = some ('a', "bc")

/-- 数字用のパーサ -/
def Parser.digit : Parser Char := sat Char.isDigit

#guard digit "123" = some ('1', "23")
#guard digit "abc" = none

/-- アルファベット小文字用のパーサ -/
def Parser.lower : Parser Char := sat Char.isLower

#guard lower "abc" = some ('a', "bc")
#guard lower "ABC" = none

/-- アルファベット大文字用のパーサ -/
def Parser.upper : Parser Char := sat Char.isUpper

#guard upper "ABC" = some ('A', "BC")
#guard upper "abc" = none

/-- アルファベット用のパーサ -/
def Parser.letter : Parser Char := sat Char.isAlpha

#guard letter "abc" = some ('a', "bc")
#guard letter "123" = none
#guard letter "ABC" = some ('A', "BC")

/-- アルファベットまたは数字用のパーサ -/
def Parser.alphanum : Parser Char := sat Char.isAlphanum

#guard alphanum "abc" = some ('a', "bc")
#guard alphanum "123" = some ('1', "23")
#guard alphanum "!" = none

/-- 指定された文字用のパーサ -/
def Parser.char (c : Char) : Parser Char := sat (· = c)

#guard char 'a' "abc" = some ('a', "bc")
#guard char 'a' "123" = none

/-- 指定された文字列用のパーサ -/
def Parser.string (x : String) : Parser String :=
  match x with
  | ⟨[]⟩ => pure ""
  | ⟨x :: xs⟩ => do
    let z ← char x
    let zs ← string ⟨xs⟩
    return s!"{z}" ++ zs

#guard string "abc" "abcdef" = some ("abc", "def")
#guard string "abc" "ab123" = none

variable {α : Type}
variable {m : Type → Type} [Alternative m]
instance [Inhabited α] : Inhabited (m α) := ⟨pure default⟩

set_option linter.missingDocs false in

mutual
  partial def Alternative.many (x : m α) : m (List α) :=
    Alternative.some x <|> pure []

  partial def Alternative.some (p : m α) : m (List α) :=
    pure (· :: ·) <*> p <*> Alternative.many p
end

/-- 識別子用のパーサ -/
def Parser.ident : Parser String := do
  let x ← lower
  let xs ← Alternative.many alphanum
  return ⟨x :: xs⟩

#guard ident "abc def" = some ("abc", " def")
#guard ident "123 def" = none

/-- 自然数のパーサ -/
def Parser.nat : Parser Nat := do
  let xs ← Alternative.some digit
  return xs.foldl (· * 10 + ·.toNat - '0'.toNat) 0

#guard nat "123 abc" = some (123, " abc")
#guard nat "abc 123" = none

/-- 空白文字のパーサ -/
def Parser.space : Parser Unit := do
  let _ ← Alternative.many <| sat Char.isWhitespace
  pure ()

#guard space "  abc" = some ((), "abc")
#guard space "abc" = some ((), "abc")

/-- 整数のパーサ -/
def Parser.int : Parser Int :=
  let negParser : Parser Int := do
    let _ ← char '-'
    let n : Int := (← nat)
    return -n
  negParser <|> (Int.ofNat <$> nat)

#guard int "-123 abc" = some (-123, " abc")
#guard int "123 abc" = some (123, " abc")
#guard int "abc 123" = none
