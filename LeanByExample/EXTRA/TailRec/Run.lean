/-
EXTRA/TailRec.lean のメモリ使用量の違いを確認するコード。
-/

def runTailRec (mode : String) : IO IO.Process.Output := do
  IO.Process.output {
    cmd := "lean"
    args := #[
      "--memory",
      "300",
      "--run",
      "LeanByExample/EXTRA/TailRec.lean",
      mode
    ]
  }

def main : IO Unit := do
  let trOut ← runTailRec "tr"
  unless trOut.exitCode == 0 do
    throw <| IO.userError s!"末尾再帰なのにエラーになりました: {trOut.stderr}"
  IO.println "テスト成功: 末尾再帰なのでエラーにならない"

  let nonTrOut ← runTailRec "nontr"
  unless nonTrOut.exitCode != 0 do
    throw <| IO.userError s!"末尾再帰でないのにエラーになりませんでした: {nonTrOut.stdout}"
  IO.println "テスト成功: 末尾再帰でないのでエラーになる"

/--
info: テスト成功: 末尾再帰なのでエラーにならない
テスト成功: 末尾再帰でないのでエラーになる
-/
#guard_msgs in --#
#eval main
