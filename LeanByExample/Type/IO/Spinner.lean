def spinnerFrames : Array String :=
  #["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]

/-- ターミナルに対して、現在のカーソルがある行全体を消せと指示する -/
def IO.clearLine : IO Unit := do
  IO.print "\r\x1b[2K"

def main : IO Unit := do
  -- 標準出力ストリームを取得する
  let stdout ← IO.getStdout

  for i in List.range 80 do
    let frame := spinnerFrames[i % spinnerFrames.size]!
    IO.print s!"\r{frame} 処理中..."

    -- 標準出力への変更をすぐに反映させる
    stdout.flush

    -- ここに「少しずつ進む重い処理」を書く
    IO.sleep 20

  -- 行を消して完了表示
  IO.clearLine
  IO.println "完了"
