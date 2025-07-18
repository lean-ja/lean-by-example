import Playground.PIH.MyStd.IO

/-- キーボードから文字列を読み込んで、その長さを表示する -/
def main : IO Unit := do
  IO.print "Enter a string: "
  let input ← IO.getInput
  IO.println s!"The entered string is \"{input}\"."
  IO.println s!"The string has {input.length} characters."
