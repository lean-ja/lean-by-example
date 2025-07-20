import Playground.Monkey.Lexer.Lexer
import Playground.Monkey.Token.Token

open Token Lexer

/-- NestToken 関数をテストする -/
def testNextToken (input : String) (expected : Array Token) : IO Unit := do
  let mut l : Lexer := Lexer.new input
  let mut actualTokens : Array Token := #[]

  while True do
    let ⟨tok, l'⟩ := l.nextToken |>.run
    l := l'
    actualTokens := actualTokens.push tok
    if tok = EOF then break

  if actualTokens.size ≠ expected.size then
    throw <| .userError s!"tests failed: - token count wrong. expected={expected.size}, got={actualTokens.size}"

  let testCases := Array.zip expected actualTokens

  for ⟨exp, actual⟩ in testCases do
    if exp ≠ actual then
      throw <| .userError s!"tests failed: - token wrong. expected={exp}, got={actual}"

  IO.println s!"ok!"

#eval testNextToken
  (input := "=+(){},;")
  (expected := #[
    ASSIGN,
    PLUS,
    LPAREN,
    RPAREN,
    LBRACE,
    RBRACE,
    COMMA,
    SEMICOLON,
    EOF
  ])

#eval testNextToken
  (input := "let five = 5;
  let ten = 10;
  let add = fn(x, y) {
  x + y;
  };
  let result = add(five, ten);
  ")
  (expected := #[
    LET,
    IDENT "five",
    ASSIGN,
    INT 5,
    SEMICOLON,
    LET,
    IDENT "ten",
    ASSIGN,
    INT 10,
    SEMICOLON,
    LET,
    IDENT "add",
    ASSIGN,
    FUNCTION,
    LPAREN,
    IDENT "x",
    COMMA,
    IDENT "y",
    RPAREN,
    LBRACE,
    IDENT "x",
    PLUS,
    IDENT "y",
    SEMICOLON,
    RBRACE,
    SEMICOLON,
    LET,
    IDENT "result",
    ASSIGN,
    IDENT "add",
    LPAREN,
    IDENT "five",
    COMMA,
    IDENT "ten",
    RPAREN,
    SEMICOLON,
    EOF
  ])

#eval testNextToken
  (input := "!-/*5;
  5 < 10 > 5;")
  (expected := #[
    BANG,
    MINUS,
    SLASH,
    ASTERISK,
    INT 5,
    SEMICOLON,
    INT 5,
    LT,
    INT 10,
    GT,
    INT 5,
    SEMICOLON,
    EOF
  ])

-- return とか true とかのテスト
#eval testNextToken
  (input := "if (5 < 10) {
  return true;
  } else {
  return false;
  }")
  (expected := #[
    IF,
    LPAREN,
    INT 5,
    LT,
    INT 10,
    RPAREN,
    LBRACE,
    RETURN,
    TRUE,
    SEMICOLON,
    RBRACE,
    ELSE,
    LBRACE,
    RETURN,
    FALSE,
    SEMICOLON,
    RBRACE,
    EOF
  ])

-- `==` とか `!=` とかのテスト
#eval testNextToken
  (input := "10 == 10;
  10 != 9;")
  (expected := #[
    INT 10,
    EQ,
    INT 10,
    SEMICOLON,
    INT 10,
    NOT_EQ,
    INT 9,
    SEMICOLON,
    EOF
  ])
