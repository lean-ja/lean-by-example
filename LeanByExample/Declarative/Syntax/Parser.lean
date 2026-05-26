-- Parser.lean ファイル

import LeanByExample.Declarative.Syntax.Environment

open Lean Elab Term Command

/-- Leanのマクロ展開ルールを使って、`input : String` から `Arith` の項を生成する -/
def TermElabM.parseArith (input : String) : TermElabM (Except String Arith) := do
  let stx := Parser.runParserCategory env_of_arith_stx `term s!"[arith| {input}]"
  match stx with
  | .error err => return Except.error err
  | .ok stx =>
    let result ← unsafe evalTerm Arith (.const ``Arith []) stx
    return Except.ok result

/-- `TermElabM` に包まれた値をむりやり取り出す -/
unsafe def TermElabM.unsafeRun {α : Type} [Inhabited α] (env : Environment) (m : TermElabM α) : α :=
  let core := liftCommandElabM <| liftTermElabM m
  let ctx : ContextInfo := { env := env, fileMap := ⟨"", #[]⟩, ngen := { } }
  let io := ContextInfo.runCoreM ctx core
  match unsafeIO io with
  | .error e => panic! s!"{e}"
  | .ok a => a

/-- 文字列をパースして`Arith`の項を生成する -/
def parseArith (s : String) : Except String Arith := unsafe
  TermElabM.unsafeRun env_of_arith_stx (TermElabM.parseArith s)


-- パーサーのテストのためのコード
section ParserTest

open Arith

instance : ToString Op where
  toString := fun op =>
    match op with
    | Op.add => "+"
    | Op.mul => "*"

/-- `Arith`を文字列化する。ただし、全体を括弧で囲う。-/
protected def Arith.toStringAux (arith : Arith) : String :=
  match arith with
  | Arith.val n => toString n
  | Arith.app op lhs rhs =>
    "(" ++ Arith.toStringAux lhs ++ s!" {op} " ++ Arith.toStringAux rhs ++ ")"

protected def Arith.toString (arith : Arith) : String :=
  match arith with
  | Arith.val n => toString n
  | Arith.app op lhs rhs =>
    Arith.toStringAux lhs ++ s!" {op} " ++ Arith.toStringAux rhs

instance : ToString Arith where
  toString := Arith.toString

private def testParseArith (input : String) (expected : Arith) : IO Unit := do
  let .ok actual := parseArith input
    | throw <| .userError s!"{input} のパースに失敗しました"

  if expected != actual then
    throw <| .userError s!"{input} のパース結果が期待値と一致しません。期待値: {expected}, 実際の値: {actual}"
  IO.println s!"✅ テスト成功!"

#eval testParseArith "1 + 2" (app Op.add (val 1) (val 2))

#eval testParseArith "3 * (4 + 5)" (app Op.mul (val 3) (app Op.add (val 4) (val 5)))

end ParserTest
