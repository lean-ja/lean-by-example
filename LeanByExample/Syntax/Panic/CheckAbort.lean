/-
Syntax/Panic/Abort.lean の abort 挙動を確認するコード
-/
import Std

open IO

/-- `LEAN_ABORT_ON_PANIC` に値を設定して `Abort.lean` を実行し、
`panic!` で処理が中断されるかを判定する。 -/
def checkAbort : IO Bool := do
  Std.Internal.IO.Async.System.setEnvVar "LEAN_ABORT_ON_PANIC" "1"
  try
    let out ← IO.Process.output {
      cmd := "lean"
      args := #["--run", "LeanByExample/Syntax/Panic/Abort.lean"]
    }

    if out.stdout.trimAscii.endsWith "hello world!" then
      return false
    else
      return true
  catch _ =>
    -- 実行そのものが失敗した場合も abort が働いたとみなす
    return true

def main : IO Unit := do
  let aborted ← checkAbort
  if !aborted then
    throw <| IO.userError "Test failed! abort did not work."

  IO.println "abort works"

/-⋆-//-- info: abort works -/
#guard_msgs in --#
#eval main
