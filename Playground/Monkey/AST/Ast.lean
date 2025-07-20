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


/-- 式 -/
declare_syntax_cat monkey_expr

section monkey_expr
  /-- 識別子 -/
  syntax ident : monkey_expr
  /-- 数値リテラル -/
  syntax num : monkey_expr
  /-- 加算 -/
  syntax:50 monkey_expr:50 "+" monkey_expr:51 : monkey_expr
  /-- 減算 -/
  syntax:50 monkey_expr:50 "-" monkey_expr:50 : monkey_expr
  /-- 前置演算子 -/
  syntax:100 "-" monkey_expr:100 : monkey_expr
  /-- 乗算 -/
  syntax:70 monkey_expr:70 "*" monkey_expr:71 : monkey_expr
  /-- 丸括弧 -/
  syntax "(" monkey_expr:15 ")" : monkey_expr
end monkey_expr

syntax "[monkey_expr|" monkey_expr "]" : term

section Syntax2AST

  open Lean Elab Term Syntax

  def Lean.TSyntax.toStrLit (stx : TSyntax `ident) : StrLit :=
    stx.getId.toString |> Syntax.mkStrLit

  macro_rules
    | `([monkey_expr| $n:num ]) => `(Expression.num $n)
    | `([monkey_expr| $name:ident ]) =>
      let nameStr : StrLit := name.toStrLit
      `(Expression.ident $nameStr)
    | `([monkey_expr| $l + $r ]) =>
      `(Expression.infix [monkey_expr| $l ] Token.PLUS [monkey_expr| $r ])
    | `([monkey_expr| $l - $r ]) =>
      `(Expression.infix [monkey_expr| $l ] Token.MINUS [monkey_expr| $r ])
    | `([monkey_expr| $l * $r ]) =>
      `(Expression.infix [monkey_expr| $l ] Token.ASTERISK [monkey_expr| $r ])
    | `([monkey_expr| - $e ]) =>
      `(Expression.prefix Token.MINUS [monkey_expr| $e ])
    | `([monkey_expr| ( $e:monkey_expr ) ]) => `([monkey_expr| $e ])

end Syntax2AST

#eval toString [Statement.exprStmt [monkey_expr| -a * b ]]

#eval toString ([Statement.letStmt "myVar" Expression.notImplemented] : Program)
