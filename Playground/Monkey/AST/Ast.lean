import Playground.Monkey.Token.Token

/-- 式 -/
inductive Expression where
  /-- 識別子 -/
  | ident (name : String) : Expression
  /-- 整数リテラル -/
  | num (value : Int) : Expression
  /-- 前置演算子 -/
  | prefix (operator : Token) (right : Expression) : Expression
  /-- 中置演算子 -/
  | infix (left : Expression) (operator : Token) (right : Expression) : Expression
  /-- `Expression` の未実装の部分を表す -/
  | notImplemented
deriving Repr, DecidableEq

/-- Expression を文字列に変換する -/
def Expression.toString (e : Expression) : String :=
  match e with
  | .ident name => s!"{name}"
  | .num value => s!"{value}"
  | .prefix operator right => s!"({operator}{Expression.toString right})"
  | .infix left operator right => s!"({Expression.toString left} {operator} {Expression.toString right})"
  | .notImplemented => "notImplemented"

instance : ToString Expression where
  toString e := e.toString

/-- 文。本文とは異なる実装を採用しており、`statementNode()` に相当するものは不要。-/
inductive Statement where
  /-- let 文 -/
  | letStmt (name : String) (value : Expression) : Statement
  /-- return 文 -/
  | returnStmt (returnValue : Expression) : Statement
  /-- 式文。式だけからなる行を持たせるために必要 -/
  | exprStmt (expr : Expression) : Statement
  /-- Statement の未実装の部分を表す -/
  | notImplemented
deriving Repr, DecidableEq

private def Statement.toString (stmt: Statement) : String :=
  match stmt with
  | .letStmt name value => s!"let {name} = {value}"
  | .returnStmt returnValue => s!"return {returnValue}"
  | .exprStmt expr => s!"{expr}"
  | .notImplemented => "notImplemented"

instance : ToString Statement where
  toString s := s.toString

/-- AST のノード -/
inductive Node where
  /-- 文 -/
  | ofStmt (s : Statement) : Node
  /-- 式 -/
  | ofExpr (e : Expression) : Node

/-- プログラムを文の集まりとして定義する。AST に相当する。-/
abbrev Program := List Statement

instance : ToString Program where
  toString p := p.map Statement.toString |>.foldl (· ++ ·) ""

private def «-a * b» : Program :=
  [Statement.exprStmt (Expression.infix (Expression.prefix Token.MINUS (Expression.ident "a")) Token.ASTERISK (Expression.ident "b"))]

#eval toString «-a * b»

#eval toString ([Statement.letStmt "myVar" Expression.notImplemented] : Program)
