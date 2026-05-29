/-

Type/IO/Greet.lean に入力を与えて実行するコード
-/

open IO

/-- `Greet.lean` を `lean --run` で実行し、標準入力として名前を渡す。 -/
def runGreet : IO Unit := do
  let rootPath := "LeanByExample/Type/IO"
  let out ← IO.Process.output
    (args := {
      cmd := "lean"
      args := #["--run", s!"{rootPath}/Greet.lean"]
    })
    (input? := some "Lean")

  unless out.exitCode == 0 do
    throw <| IO.userError s!"`lean --run` の実行に失敗しました: {out.stderr}"

  IO.println out.stdout.trimAscii

/-⋆-//-- info: 誰に挨拶しますか？
Hello, Lean! -/
#guard_msgs in --#
#eval runGreet
