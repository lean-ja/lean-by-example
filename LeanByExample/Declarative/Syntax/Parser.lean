import LeanByExample.Declarative.Syntax.Environment

open Lean Elab Term Command

/-- `Syntax`から`Arith`を復元する -/
partial def mkArith (stx : Syntax) : Except String Arith :=
  match stx with
  | `(arith| $n:num) =>
    return Arith.val n.getNat
  | `(arith| $l:arith + $r:arith) => do
    return Arith.app Op.add (← mkArith l) (← mkArith r)
  | `(arith| $l:arith * $r:arith) => do
    return Arith.app Op.mul (← mkArith l) (← mkArith r)
  | `(arith| ($e:arith)) => mkArith e
  | _ => throw s!"unexpected syntax: {stx}"

/-- 文字列をパースして`Arith`の項を生成する -/
def parseArith (s : String) : Except String Arith := do
  let stx ← Parser.runParserCategory env_of_arith_stx `arith s
  mkArith stx

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
