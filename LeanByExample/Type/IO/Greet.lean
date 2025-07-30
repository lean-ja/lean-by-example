/-- 標準入力から入力された名前に対して挨拶をする -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "誰に挨拶しますか？"
  let input ← stdin.getLine
  let name := input.trim -- これをしないと余計な改行が入る

  stdout.putStrLn s!"Hello, {name}!"
