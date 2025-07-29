open IO FS System

/-- シンプルな `cat` コマンドの実装。

コマンドライン引数からファイル名を受け取り、そのファイルの内容を表示する。
ファイル名が指定されていない場合や、複数指定された場合にはエラーメッセージを表示する。
-/
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
