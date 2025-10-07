import Lean
import LeanByExample.Environment

open Lean

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
def parseArithOfEnv (s : String) (env : Environment) : Except String Arith := do
  let stx ← Parser.runParserCategory env `arith s
  let arith ← mkArith stx
  return arith

/-- 文字列をパースして`Arith`の項を生成する -/
def parseArith (s : String) : Except String Arith := do
  parseArithOfEnv s environment

#eval parseArith "1 + 2 * 3"
