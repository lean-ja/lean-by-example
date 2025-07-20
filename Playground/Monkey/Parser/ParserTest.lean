import Playground.Monkey.Lexer.Lexer
import Playground.Monkey.Parser.Parser

/-- 一般的な `let` 文に対する parser のテスト -/
def testLetStatement (stmt : Statement) (expectedId : String) : IO Bool := do
  let .letStmt actualId _val := stmt
    | throw <| .userError s!"not expected statement. got={stmt}, expected=Stmt.letStmt"

  -- 期待される識別子と実際の識別子が一致するか
  if actualId != expectedId then
    throw <| .userError s!"not expected identifier. got={actualId} expected={expectedId}"

  return true

/-- Parser にエラーが一つでもあれば全部出力する -/
def checkParserErrors (p : Parser) : IO Unit := do
  if p.errors.isEmpty then
    return

  throw <| .userError (String.intercalate "\n" p.errors)

/-- 具体的な `let` 文に対する parser のテスト -/
def testLetStatements : IO Unit := do
  let input := "
    let x = 5;
    let y = 10;
    let foobar = 838383;"

  let l := Lexer.new input
  let p := Parser.new l

  let ⟨result, parser⟩ := p.parseProgram
  checkParserErrors parser

  let some program := result | IO.eprintln s!"ParseProgram returned none"
  IO.println s!"given program={program}"

  -- 入力の文はちょうど３つのはず
  if program.length != 3 then
    throw <| .userError s!"program.Statements does not contain 3 statements. got={program.length}"

  -- 期待される識別子
  let expectedId := ["x", "y", "foobar"]
  for (id, stmt) in List.zip expectedId program do
    if ! (← testLetStatement stmt id) then
      throw <| .userError s!"testLetStatement failed"

  IO.println "ok!"

#eval testLetStatements


/-- 具体的な return 文に対するテスト -/
def testReturnStatements : IO Unit := do
  let input := "
    return 5;
    return 10;
    return 993322;"

  let l := Lexer.new input
  let p := Parser.new l

  let ⟨result, parser⟩ := p.parseProgram
  checkParserErrors parser

  let some program := result | IO.eprintln s!"ParseProgram returned none"
  IO.println s!"given program={program}"

  -- 入力の文はちょうど３つのはず
  if program.length != 3 then
    throw <| .userError s!"program.Statements does not contain 3 statements. got={program.length}"

  -- return 文だけで構成されていることを確かめる
  for stmt in program do
    let .returnStmt _val := stmt
      | throw <| .userError s!"not expected statement. got={stmt}, expected=Stmt.returnStmt"

#eval testReturnStatements


/-- 一般的な識別子に対するテスト -/
def testIdentifierExpression : IO Unit := do
  let input := "foobar;"

  let l := Lexer.new input
  let p := Parser.new l
  let ⟨result, parser⟩ := p.parseProgram
  checkParserErrors parser

  let some program := result
    | IO.eprintln s!"ParseProgram returned none"

  if program.length != 1 then
    throw <| .userError s!"program length is not equal to 1. got={program.length}"

  let [Statement.exprStmt stmt] := program
    | throw <| .userError s!"Statement.exprStmt is expected. got={program}"

  let Expression.ident id := stmt
    | throw <| .userError s!"Expression.identifier is expected. got={stmt}"

  if id != "foobar" then
    throw <| .userError s!"ident is expected to be 'foobar'. got={id}"
  IO.println "ok!"

#eval testIdentifierExpression

/-- 整数リテラルに対するテスト -/
def testIntegerLiteralExpression : IO Unit := do
  let input := "5;"

  let l := Lexer.new input
  let p := Parser.new l
  let ⟨result, parser⟩ := p.parseProgram
  checkParserErrors parser

  let some program := result
    | IO.eprintln s!"ParseProgram returned none"

  if program.length != 1 then
    throw <| .userError s!"program length is not equal to 1. got={program.length}"

  let [Statement.exprStmt stmt] := program
    | throw <| .userError s!"Statement.exprStmt is expected. got={program}"

  let Expression.num value := stmt
    | throw <| .userError s!"Expression.num is expected. got={stmt}"

  if value != 5 then
    throw <| .userError s!"value is expected to be 5. got={value}"
  IO.println "ok!"

#eval testIntegerLiteralExpression

private structure PrefixTestCase where
  input : String
  operator : Token
  integer : Int

/-- 前置演算子に対するテスト -/
def testParsingPrefixExpressions : IO Unit := do
  let prefixTests : Array PrefixTestCase := #[
    { input := "!5;", operator := .BANG, integer := 5 },
    { input := "-15;", operator := .MINUS, integer := 15 }
  ]

  for testCase in prefixTests do
    let l := Lexer.new testCase.input
    let p := Parser.new l
    let ⟨result, parser⟩ := p.parseProgram
    checkParserErrors parser

    let some program := result
      | IO.eprintln s!"ParseProgram returned none"

    if program.length != 1 then
      throw <| .userError s!"program.Statements does not contain 1 statement. got={program.length}"

    let [Statement.exprStmt stmt] := program
      | throw <| .userError s!"Statement.exprStmt is expected. got={program}"

    let Expression.prefix operator right := stmt
      | throw <| .userError s!"Expression.prefix is expected. got={stmt}"

    if operator != testCase.operator then
      throw <| .userError s!"operator is expected to be {testCase.operator}. got={operator}"

    let Expression.num value := right
      | throw <| .userError s!"Expression.num is expected. got={right}"

    if value != testCase.integer then
      throw <| .userError s!"value is expected to be {testCase.integer}. got={value}"

  IO.println "ok!"

#eval testParsingPrefixExpressions

private structure InfixTestCase where
  input : String
  leftValue : Int
  operator : Token
  rightValue : Int

/-- 中置演算子式のパースのテスト -/
def testParsingInfixExpressions : IO Unit := do
  let infixTests : Array InfixTestCase := #[
    { input := "5 + 5;", leftValue := 5, operator := .PLUS, rightValue := 5 },
    { input := "5 - 5;", leftValue := 5, operator := .MINUS, rightValue := 5 },
    { input := "5 * 5;", leftValue := 5, operator := .ASTERISK, rightValue := 5 },
    { input := "5 / 5;", leftValue := 5, operator := .SLASH, rightValue := 5 },
    { input := "5 > 5;", leftValue := 5, operator := .GT, rightValue := 5 },
    { input := "5 < 5;", leftValue := 5, operator := .LT, rightValue := 5 },
    { input := "5 == 5;", leftValue := 5, operator := .EQ, rightValue := 5 },
    { input := "5 != 5;", leftValue := 5, operator := .NOT_EQ, rightValue := 5 }
  ]

  for testCase in infixTests do
    let l := Lexer.new testCase.input
    let p := Parser.new l
    let ⟨result, parser⟩ := p.parseProgram
    checkParserErrors parser

    let some program := result
      | IO.eprintln s!"ParseProgram returned none"

    if program.length != 1 then
      throw <| .userError s!"program.Statements does not contain 1 statement. got={program.length}"

    let [Statement.exprStmt stmt] := program
      | throw <| .userError s!"Statement.exprStmt is expected. got={program}"

    let Expression.infix left operator right := stmt
      | throw <| .userError s!"Expression.infix is expected. got={stmt}"

    let Expression.num leftValue := left
      | throw <| .userError s!"Expression.num is expected. got={left}"

    let Expression.num rightValue := right
      | throw <| .userError s!"Expression.num is expected. got={right}"

    if operator != testCase.operator then
      throw <| .userError s!"operator is expected to be {testCase.operator}. got={operator}"

    if leftValue != testCase.leftValue then
      throw <| .userError s!"leftValue is expected to be {testCase.leftValue}. got={leftValue}"

    if rightValue != testCase.rightValue then
      throw <| .userError s!"rightValue is expected to be {testCase.rightValue}. got={rightValue}"

  IO.println "ok!"

#eval testParsingInfixExpressions

private structure PrecedenceTestCase where
  input : String
  expected : String

/-- AST に演算子の優先度が正しく反映されていることの確認 -/
def testOperatorPrecedenceParsing : IO Unit := do
  let tests : Array PrecedenceTestCase := #[
    { input := "-a * b", expected := "((-a) * b)" },
    { input := "!-a", expected := "(!(-a))" },
    { input := "a + b + c", expected := "((a + b) + c)" },
    { input := "a + b - c", expected := "((a + b) - c)" },
    { input := "a * b * c", expected := "((a * b) * c)" },
    { input := "a * b / c", expected := "((a * b) / c)" },
    { input := "a + b / c", expected := "(a + (b / c))" },
    { input := "a + b * c + d / e - f", expected := "(((a + (b * c)) + (d / e)) - f)" },
    { input := "3 + 4; -5 * 5", expected := "(3 + 4)((-5) * 5)" },
    { input := "5 > 4 == 3 < 4", expected := "((5 > 4) == (3 < 4))" },
    { input := "5 < 4 != 3 > 4", expected := "((5 < 4) != (3 > 4))" },
    { input := "3 + 4 * 5 == 3 * 1 + 4 * 5", expected := "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))" }
  ]

  for testCase in tests do
    let l := Lexer.new testCase.input
    let p := Parser.new l
    let ⟨result, parser⟩ := p.parseProgram
    checkParserErrors parser

    let some program := result
      | IO.eprintln s!"ParseProgram returned none"

    let actual := ToString.toString program
    if actual != testCase.expected then
      throw <| .userError s!"not expected. got={actual}, expected={testCase.expected}"

  IO.println "ok!"

#eval testOperatorPrecedenceParsing

/-- 識別子のテストのためのヘルパー関数

* `exp` はテスト対象の式
* `value` は期待される識別子の値
-/
def testIdentifier (exp : Expression) (value : String) : IO Bool := do
  let Expression.ident name := exp
    | throw <| .userError s!"identifier is expected, but got={exp}"

  if name != value then
    throw <| .userError s!"identifier is expected to be {value}, but got={name}"

  return true

/-- 整数リテラルのテスト -/
def testIntegerLiteral (il : Expression) (value : Int) : IO Bool := do
  let Expression.num integ := il
    | throw <| .userError s!"num is expected, but got={il}"

  if integ != value then
    throw <| .userError s!"num is expected to be {value}, but got={integ}"

  return true

/-- リテラルのためのテストヘルパー型クラス -/
class TestLiteralExpression (α : Type) where
  /-- 多相的なテストヘルパー -/
  test : Expression → α → IO Bool

instance : TestLiteralExpression Int where
  test := testIntegerLiteral

instance : TestLiteralExpression String where
  test := testIdentifier

/-- 中置演算子のテストのためのヘルパー関数 -/
def testInfixExpression {α : Type} [TestLiteralExpression α]
    (exp : Expression) (left : α) (operator : String) (right : α) : IO Bool := do

  let Expression.infix l op r := exp
    | throw <| .userError s!"infix expression is expected, but got={exp}"

  let _ ← TestLiteralExpression.test l left

  if toString op != operator then
    throw <| .userError s!"operator is expected to be {operator}, but got={op}"

  let _ ← TestLiteralExpression.test r right

  return true
