/-- キーボードからユーザの入力を取得する -/
def getUserInput : IO String := do
  -- 入力待ちであることをアピールする
  IO.print "> "
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  -- trim をしないと余計な改行が入る
  return input.trimAscii.copy

/-- 標準入力から入力された名前に対して挨拶をする -/
def main : IO Unit := do
  IO.println "誰に挨拶しますか？"
  let name ← getUserInput
  IO.println s!"Hello, {name}!"
