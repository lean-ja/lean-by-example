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

open Arith

-- パーサーのテスト
#guard
  let expected := app Op.add (val 1) (val 2)
  let actual := parseArith "1 + 2"
  match actual with
  | Except.error _ => false
  | Except.ok actual =>
    expected == actual

#guard
  let expected := app Op.mul (val 3) (app Op.add (val 4) (val 5))
  let actual := parseArith "3 * (4 + 5)"
  match actual with
  | Except.error _ => false
  | Except.ok actual =>
    expected == actual
