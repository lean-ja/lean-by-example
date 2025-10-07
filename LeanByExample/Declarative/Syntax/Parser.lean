import LeanByExample.Declarative.Syntax.Environment

open Lean Elab Term Command

/-- evalTerm で Syntax から Arith を取り出す -/
def parseArithCoreM (input : String) : CoreM Arith := liftCommandElabM <| liftTermElabM do
  let env ← getEnv
  let stx ← ofExcept <| Parser.runParserCategory env `term s!"[arith| {input}]"
  let result ← unsafe evalTerm Arith (.const ``Arith []) stx
  return result

/-- runCoreM で CoreM を IO にする -/
def parseArithIO (input : String) : IO Arith := do
  let ctx : ContextInfo := { env := env_of_arith_stx, fileMap := ⟨"", #[]⟩, ngen := { } }
  ContextInfo.runCoreM ctx <| parseArithCoreM input

/-- 文字列をパースして`Arith`の項を生成する -/
def parseArith (input : String) : Except String Arith := unsafe do
  parseArithIO input
  |> unsafeIO
  |>.mapError toString

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
