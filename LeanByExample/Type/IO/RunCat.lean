/-

Type/IO/Cat.lean に入力を与えて実行するコード
-/

open IO

/-- `Cat.lean` を `lean --run` で実行し、`Test.txt` を入力として渡す。 -/
def runCat : IO Unit := do
  let rootPath := "LeanByExample/Type/IO"
  let out ← IO.Process.output {
    cmd := "lean"
    args := #[
      "--run",
      s!"{rootPath}/Cat.lean",
      s!"{rootPath}/Test.txt"
    ]
  }

  unless out.exitCode == 0 do
    throw <| IO.userError s!"`lean --run` の実行に失敗しました: {out.stderr}"

  IO.println out.stdout.trimAscii

/-⋆-//-- info: Lean is nice! -/
#guard_msgs in --#
#eval runCat
