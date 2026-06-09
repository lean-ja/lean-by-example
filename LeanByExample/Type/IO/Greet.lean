/-- 標準入力から入力された名前に対して挨拶をする -/
def main : IO Unit := do
  let stdin ← IO.getStdin

  IO.println "誰に挨拶しますか？"
  IO.print "> "
  let input ← stdin.getLine
  let name := input.trimAscii.copy -- これをしないと余計な改行が入る

  IO.println s!"Hello, {name}!"
