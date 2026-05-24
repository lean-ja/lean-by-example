import Lean

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド

注意: このコマンドを import して使用すると lean4 web 上で実行する機能が使えなくなってしまう。
このコマンドを import する場合は、そのファイルの内容を md としてインポートするなどの工夫が必要。
-/
elab "#doc " x:ident : command => do
  let name := x.getId
  if let some s ← findDocString? (← getEnv) name then
    logInfo m!"{s}"
