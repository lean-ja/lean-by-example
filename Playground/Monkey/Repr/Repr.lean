import Playground.Monkey.Lexer.Lexer
import Playground.Monkey.Token.Token

open IO Token

/-- REPL を表す。
`lake env lean --run Monkey/Repl/Repl.lean` で実行できる。
標準入力に入れた Monkey のコードを読みこむ。 -/
partial def main : IO Unit := do
  IO.print ">> "
  let inputStream ← getStdin
  let input ← inputStream.getLine
  if input.trim = "" then return ()

  let mut l : Lexer := Lexer.new input
  let mut tokens : Array Token := #[]

  while True do
    let ⟨tok, l'⟩ := l.nextToken |>.run
    l := l'
    tokens := tokens.push tok
    if tok = EOF then break

  IO.println tokens
  main
