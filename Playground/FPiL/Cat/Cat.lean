/- ファイルが存在するかどうかを判定できるようになったら、
ファイルが存在するときに「ファイルの中身を読んで出力する」処理を追加すれば
簡単な cat コマンドができます。
-/

open IO FS System

/-- めちゃくちゃシンプルなcatコマンドの実装 -/
def main (args : List String) : IO Unit := do
  match args with
  | [] => println "ファイル名を指定してください。"
  | [fileName] =>
    let filePath : FilePath := fileName
    let fileExists ← filePath.pathExists
    if fileExists then
      let contents ← readFile filePath
      println contents
    else
      println s!"ファイルは存在しません: {fileName}"
  | _ => println "複数のファイル名は指定できません。1つだけ指定してください。"
