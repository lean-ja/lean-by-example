import Lean

/-- トークン

本にある Token の定義では structure になっていたので、
literal が必要ないのときでも literal の情報があって冗長だった。
それを修正した定義にしている。 -/
inductive Token where
  /-- 識別子 -/
  | IDENT (name : String)
  /-- 数値リテラル -/
  | INT (value : Int)
  /-- 受け入れ不能エラー -/
  | ILLEGAL
  /-- ファイル終端 -/
  | EOF
  /-- 代入記号 "=" -/
  | ASSIGN
  /-- 足し算記号 + -/
  | PLUS
  /-- コンマ , -/
  | COMMA
  /-- セミコロン ; -/
  | SEMICOLON
  /-- 開き括弧 ( -/
  | LPAREN
  /-- 閉じ括弧 ) -/
  | RPAREN
  /-- 開き波括弧 -/
  | LBRACE
  /-- 閉じ波括弧 -/
  | RBRACE
  /-- 無名関数 fn -/
  | FUNCTION
  /-- LET キーワード -/
  | LET
  /-- 引き算記号 "-" -/
  | MINUS
  /-- ビックリマーク ! -/
  | BANG
  /-- アスタリスク * -/
  | ASTERISK
  /-- スラッシュ "/" -/
  | SLASH
  /-- 小なり "<" -/
  | LT
  /-- 大なり ">" -/
  | GT
  /-- 等号 `==` -/
  | EQ
  /-- 等しくない `!=` -/
  | NOT_EQ
  /-- true : Bool -/
  | TRUE
  /-- false : Bool -/
  | FALSE
  /-- IF キーワード -/
  | IF
  /-- ELSE キーワード -/
  | ELSE
  /-- RETURN キーワード -/
  | RETURN
deriving Repr, BEq, DecidableEq, Hashable

/-- Token が同じ種類であるかどうか判定する -/
def Token.sameType (t1 t2 : Token) : Bool :=
  match t1, t2 with
  | .IDENT _, .IDENT _ => true
  | .INT _, .INT _ => true
  | _, _ => t1 = t2

/-- `ILLEGAL` を初期値にする -/
instance : Inhabited Token := ⟨Token.ILLEGAL⟩

private def Token.toString (t : Token) : String :=
  match t with
  | .ILLEGAL => "ILLEGAL"
  | .EOF => "EOF"
  | .IDENT lit => lit
  | .INT lit => ToString.toString lit
  | .ASSIGN => "="
  | .PLUS => "+"
  | .COMMA => ","
  | .SEMICOLON => ";"
  | .LPAREN => "("
  | .RPAREN => ")"
  | .LBRACE => "{"
  | .RBRACE => "}"
  | .FUNCTION => "FUNCTION"
  | .LET => "LET"
  | .MINUS => "-"
  | .BANG => "!"
  | .ASTERISK => "*"
  | .SLASH => "/"
  | .LT => "<"
  | .GT => ">"
  | .EQ => "=="
  | .NOT_EQ => "!="
  | .TRUE => "TRUE"
  | .FALSE => "FALSE"
  | .IF => "IF"
  | .ELSE => "ELSE"
  | .RETURN => "RETURN"

instance : ToString Token where
  toString := Token.toString

open Lean Token

/-- 言語のキーワードを格納する辞書 -/
def keywords : Std.HashMap String Token :=
  let list : List (String × Token) := [
    ("fn", FUNCTION),
    ("let", LET),
    ("true", TRUE),
    ("false", FALSE),
    ("if", IF),
    ("else", ELSE),
    ("return", RETURN),
  ]
  Std.HashMap.ofList list

/-- 文字列をトークンに変換する。
その過程でユーザ定義の識別子なのか、言語のキーワードなのか見分ける作業を行う。-/
def lookupIdent (ident : String) : Token :=
  match keywords[ident]? with
  | some tok => tok
  | none => IDENT ident
