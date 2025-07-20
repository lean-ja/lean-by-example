import Playground.Monkey.Ast.Ast
import Playground.Monkey.Lexer.Lexer
import Lean

/-- 構文解析器 -/
structure Parser where
  /-- レキサー -/
  l : Lexer
  /-- 現在のトークン -/
  curToken : Token
  /-- 次のトークン -/
  peekToken : Token
  /-- 構文解析エラー -/
  errors : List String

/-- 前置構文解析関数 -/
def PrefixParseFn := StateM Parser <| Option Expression

/-- 中値構文解析関数 -/
def InfixParseFn := Expression → (StateM Parser <| Option Expression)

/-- パースの優先順位 -/
inductive Precedence where
  /-- 最低の優先順位 -/
  | LOWEST
  /-- 等号と同じ優先順位 -/
  | EQUALS
  /-- 不等号と同じ優先順位 -/
  | LESSGREATER
  /-- `+` と同じ優先順位 -/
  | SUM
  /-- `*` と同じ優先順位 -/
  | PRODUCT
  /-- `-` や `!` と同じ優先順位 -/
  | PREFIX
  /-- 関数呼び出しと同じ優先順位 -/
  | CALL
  deriving Ord, Inhabited

export Precedence (LOWEST EQUALS LESSGREATER SUM PRODUCT PREFIX CALL)

attribute [instance] ltOfOrd leOfOrd

/-- 各トークンの優先順位 -/
def Token.precedence : Token → Precedence
  | .EQ => EQUALS
  | .NOT_EQ => EQUALS
  | .LT => LESSGREATER
  | .GT => LESSGREATER
  | .PLUS => SUM
  | .MINUS => SUM
  | .SLASH => PRODUCT
  | .ASTERISK => PRODUCT
  | _ => LOWEST

private def Parser.toString (p : Parser) : String :=
  s!"⟨curToken={p.curToken}, peekToken={p.peekToken}⟩ : Parser"

instance : ToString Parser where
  toString := Parser.toString

/-- curToken と peekToken を次に進める -/
def Parser.nextToken : StateM Parser PUnit := do
  let p ← get
  let ⟨newToken, newLexer⟩ := p.l.nextToken
  let newParser : Parser := { p with
    l := newLexer,
    curToken := p.peekToken,
    peekToken := newToken,
    errors := p.errors
  }
  set newParser

mutual

/-- トークンタイプに応じて前置構文解析器を取得する -/
partial def prefixParseFns : Token → PrefixParseFn
  | .IDENT x => return Expression.ident x
  | .INT value => return Expression.integerLiteral value
  | tkn@.BANG | tkn@.MINUS => do
    Parser.nextToken
    let some right ← Parser.parseExpression PREFIX
      | return none
    let expr := Expression.prefix tkn right
    return expr
  | _ => do
    let p ← get
    let errmsg := s!"no prefix parse function for {p.curToken} found"
    set <| { p with errors := p.errors ++ [errmsg]}
    return none

/-- 中置演算子式をパースする -/
partial def Parser.parseInfixExpression (left : Expression) : StateM Parser <| Option Expression := do
  let oldParser ← get
  let precedence := oldParser.curToken.precedence
  Parser.nextToken
  let some right ← Parser.parseExpression precedence
    | return none
  let expression := Expression.infix left oldParser.curToken right
  return expression

/-- トークンタイプに応じて中値構文解析器を取得する -/
partial def infixParseFns : Token → InfixParseFn
  | .PLUS | .MINUS | .SLASH | .ASTERISK
  | .EQ | .NOT_EQ | .LT | .GT => Parser.parseInfixExpression
  | _ => fun left => do
    let p ← get
    let errmsg := s!"no infix parse function for {p.curToken} found"
    set <| { p with errors := p.errors ++ [errmsg]}
    return left

/-- 式をパースする -/
partial def Parser.parseExpression (precedence : Precedence) : StateM Parser <| Option Expression := do
  let prefixFn := prefixParseFns (← get).curToken

  -- パースが失敗したら `none` を返す
  let mut some leftExp ← prefixFn
    | return none

  while (← get).peekToken != Token.SEMICOLON && precedence < (← get).peekToken.precedence do
    let infixParseFn := infixParseFns (← get).peekToken
    Parser.nextToken
    let some leftExp' ← infixParseFn leftExp
      | return none
    leftExp := leftExp'

  return leftExp

end

/-- 新しくパーサを作る -/
def Parser.new (l : Lexer) : Parser :=
  -- Id モナドは無言で取り出せる
  let (curToken, l') := l.nextToken
  let (peekToken, l'') := l'.nextToken
  { l := l'', curToken, peekToken, errors := []}

/-- p の curToken が指定されたトークンと種類が一致するか -/
def Parser.curTokenIs (p : Parser) (t : Token) : Bool :=
  Token.sameType p.curToken t

/-- p の peekToken が指定されたトークンと種類が一致するか -/
def Parser.peekTokenIs (p : Parser) (t : Token) : Bool :=
  Token.sameType p.peekToken t

/-- `expectPeek` の過程でエラーが起きたときのために、
エラーメッセージを蓄積する処理 -/
def Parser.peekError (expectedToken : String) : StateM Parser Unit := do
  let p ← get
  set { p with errors := p.errors ++ [s!"expected next token to be {expectedToken.trim}, got {p.peekToken} instead"] }

open Lean Parser Term in
/-- p の peekToken が指定されたトークン `pat` と種類が一致するか判定。一致した場合は次に進める -/
macro "expectPeek " pat:term rest:doSeqItem* : doElem => do
  let pat' : StrLit := pat.raw.getSubstring?.get! |> toString |> Syntax.mkStrLit
  `(doElem| do
    let $pat := (← get).peekToken
      | Parser.peekError $pat'
        return none
    nextToken
    $rest*
  )

/-- let 文をパースする -/
def Parser.parseLetStatement : StateM Parser (Option Statement) := do
  expectPeek .IDENT name
  expectPeek .ASSIGN

  while ! (← get).curTokenIs (Token.SEMICOLON) do
    nextToken

  return Statement.letStmt name Expression.notImplemented

/-- return 文をパースする -/
def Parser.parseReturnStatement : StateM Parser (Option Statement) := do
  while ! (← get).curTokenIs (Token.SEMICOLON) do
    nextToken
  return Statement.returnStmt Expression.notImplemented

/-- 式文をパースする -/
def Parser.parseExpressionStatement : StateM Parser (Option Statement) := do
  let some expr ← parseExpression LOWEST
    | return none
  let stmt := Statement.exprStmt expr
  if (← get).peekTokenIs (Token.SEMICOLON) then
    nextToken
  return stmt

/-- 一文をパースする -/
def Parser.parseStatement : StateM Parser (Option Statement) := do
  match (← get).curToken with
  | .LET => parseLetStatement
  | .RETURN => parseReturnStatement
  | _ => parseExpressionStatement

/-- プログラムをパースする -/
def Parser.parseProgram : StateM Parser (Option Program) := do
  let mut program : Program := []

  while (← get).curToken != Token.EOF do
    let some stmt ← parseStatement
      | nextToken; continue
    program := stmt :: program
    nextToken

  program := program.reverse
  return program

#eval
  let input := "
    let x = 5;
    let y = 10;
    let foobar = 838383;"

  let l := Lexer.new input
  let p := Parser.new l

  ToString.toString (p.parseProgram |>.run |>.fst)
