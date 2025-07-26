/- `cat` コマンドを作る第一段階として、
与えられたパスのファイルが「存在するかどうか」だけを判定して、
「存在します」または「存在しません」と出力するようなCLIツールを作ります。
-/

open IO FS

def main (args : List String) : IO Unit := do
  match args with
  | [] => println "ファイル名を指定してください。"
  | [fileName] =>
    let filePath : System.FilePath := fileName
    let fileExists ← filePath.pathExists
    if fileExists then
      println s!"ファイルは存在します: {fileName}"
    else
      println s!"ファイルは存在しません: {fileName}"
  | _ => println "複数のファイル名は指定できません。1つだけ指定してください。"
