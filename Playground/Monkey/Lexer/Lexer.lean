import Playground.Monkey.Token.Token

/-- 字句解析器 -/
structure Lexer where
  /-- 入力された文字列。字句解析中は不変 -/
  input : String
  /-- 今読んでいる位置 -/
  position : Nat := 0
  /-- 次に読む位置 -/
  readPosition : Nat := 0
  /-- 現在の文字 -/
  ch : Char := '\x00'
deriving Repr

-- 空文字を表す Char
#guard ⟨0, by decide⟩ = '\x00'

-- アルファベットかどうか判定する関数
example : Char → Bool := Char.isAlpha

/-- 識別子として許可できるような文字列か？
アルファベットであるか、あるいはアンダースコア -/
def Char.isLetter (ch : Char) : Bool := ch.isAlpha || ch == '_'

namespace Lexer

/-- Lexer を１文字読み進める -/
def readChar : StateM Lexer Unit := do
  let mut l ← get
  let l' := if l.readPosition ≥ l.input.length
    then { l with ch := '\x00' }
    else { l with ch := l.input.get ⟨l.readPosition⟩}
  set { l' with position := l.readPosition, readPosition := l.readPosition + 1 }

/-- Lexer を進めることなく、入力を覗き見(peek)する `readChar` の変種 -/
def peekChar (l : Lexer) : Char :=
  if l.readPosition ≥ l.input.length then '\x00'
  else l.input.get ⟨l.readPosition⟩

/-- デフォルト値を持たせたコンストラクタの変種 -/
def mkD (input : String) (position readPosition : Nat := 0)
    (ch : Char := '\x00') : Lexer :=
  { input := input, position := position, readPosition := readPosition, ch := ch }

/-- 文字列から Lexer を初期化する -/
def new (input : String) : Lexer :=
  StateT.run readChar (Lexer.mkD input) |> Id.run |>.snd

/-- Lexer を更新しつつ、letter ではない文字列が出てくるまで読み進める -/
def readIdentifier : StateM Lexer String := do
  let mut l ← get
  let position := l.position
  while l.ch.isLetter do
    readChar
    l ← get
  return l.input
    |>.take l.position
    |>.drop position

/-- Lexer を更新しつつ、Number ではない文字列が出てくるまで読み進める -/
def readNumber : StateM Lexer Int := do
  let mut l ← get
  let position := l.position
  while l.ch.isDigit do
    readChar
    l ← get
  return l.input
    |>.take l.position
    |>.drop position
    |>.toInt!

open Token

-- Char を String に変換する関数
example : Char → String := String.singleton

-- Char が数字かどうか判定する
example : Char → Bool := Char.isDigit

/-- Lexer に空白スペースと改行を無視させる -/
def skipWhitespace : StateM Lexer Unit := do
  while (← get).ch.isWhitespace do
    readChar

/-- Lexer を更新しながら、次のトークンを読む -/
def nextToken : StateM Lexer Token := do
  skipWhitespace
  let mut l ← get

  /- 2文字トークンの処理 -/
  if l.ch == '=' && l.peekChar == '=' then
    readChar
    readChar
    return EQ

  if l.ch == '!' && l.peekChar == '=' then
    readChar
    readChar
    return NOT_EQ

  /- 1文字トークンの処理 -/
  let mut tok := match l.ch with
    | '=' => ASSIGN
    | '+' => PLUS
    | '-' => MINUS
    | '!' => BANG
    | '/' => SLASH
    | '*' => ASTERISK
    | '<' => LT
    | '>' => GT
    | '(' => LPAREN
    | ')' => RPAREN
    | '{' => LBRACE
    | '}' => RBRACE
    | ',' => COMMA
    | ';' => SEMICOLON
    | '\x00' => EOF
    | _ => ILLEGAL
  if l.ch.isLetter then
    let literal ← readIdentifier
    let token := lookupIdent literal
    return token
  else if l.ch.isDigit then
    let literal ← readNumber
    let token : Token := INT literal
    return token
  readChar
  return tok

/-- Lexer.nextToken の StateM を使用しないバージョン。
出力は、「新しく読み込んだ Token」と「更新後の Lexer」の組。
実は不要かもしれない。 -/
def runNextToken (l : Lexer) : Token × Lexer :=
  Id.run <| StateT.run Lexer.nextToken l

end Lexer
