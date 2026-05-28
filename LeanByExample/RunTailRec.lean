

def main : IO Unit := do
  let rootPath := "LeanByExample/"
  let threshold := 300
  try
    let _ ← IO.Process.output {
      cmd := "lean"
      args := #[
        "--memory",
        s!"{threshold}",
        "--run",
        s!"{rootPath}/TailRec.lean",
        "tr"
      ]
    }
    IO.println s!"✅ テスト成功: 末尾再帰なのでエラーにならない"
  catch _e =>
    throw <| IO.userError s!"エラー: 末尾再帰なのにエラーになった"

  try
    let _ ← IO.Process.output {
      cmd := "lean"
      args := #[
        "--memory",
        s!"{threshold}",
        "--run",
        s!"{rootPath}/TailRec.lean",
        "nontr"
      ]
    }
    throw <| IO.userError s!"エラー: 末尾再帰でないのにエラーにならない"
  catch _e =>
    IO.println s!"✅ テスト成功: 末尾再帰でないのでエラーになる"

#eval main
