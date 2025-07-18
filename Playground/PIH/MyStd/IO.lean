/- # Lean の標準ライブラリにあってほしい関数の定義 -/

/-- Accepts a string input from the keyboard, including the trailing newline as-is. -/
def IO.getInputln : IO String := do
  (← IO.getStdin).getLine

/-- Accepts a string input from the keyboard, removing newline characters. -/
def IO.getInput : IO String := do
  return removeBr (← getInputln)
where
  removeBr (str : String) : String := Id.run do
    if System.Platform.isWindows then
      str.dropRight 2
    else
      str.dropRight 1
