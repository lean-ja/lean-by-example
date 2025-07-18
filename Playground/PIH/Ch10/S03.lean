

open IO FS Stream

/-- ## getLine
この関数が、教科書における `getChar` に結構近い。
標準入力を受け取って、その文字を画面に表示し、その文字を結果として返す。

### 差異
* 型が `IO String` になっていて、教科書のように `IO Char` になっていない。
* `Stream` を引数に持つ。これは標準ストリームを意味しており、標準入出力を扱う。 -/
example : Stream → IO String := getLine

/-- ## IO.print
教科書における `putChar` に相当しそうな関数。
-/
example (s : String) : IO Unit := IO.print s

/-- `getLine` の使用例 -/
def main : IO Unit := do
  IO.print "What's your name?: "
  let name ← (← IO.getStdin).getLine
  IO.println s!"Hello, {name}"
