import Lean
import Qq

/-- 2項演算の集合 -/
inductive Op where
  /-- 加法 -/
  | add
  /-- 乗法 -/
  | mul
deriving DecidableEq, Repr

/-- 数式 -/
inductive Arith where
  /-- 数値リテラル -/
  | val : Nat → Arith
  /-- 演算子の適用 -/
  | app : Op → Arith → Arith → Arith
deriving DecidableEq, Repr

section Arith

  /-- `Arith` のための構文カテゴリ -/
  declare_syntax_cat arith

  /-- `Arith` を見やすく定義するための構文 -/
  syntax "[arith|" arith "]" : term

  -- 数値リテラルは数式
  syntax:max num : arith

  -- 数式を `+` または `*` で結合したものは数式
  -- `+` と `*` のパース優先順位を指定しておく
  syntax:30 arith:30 " + " arith:31 : arith
  syntax:35 arith:35 " * " arith:36 : arith

  -- 数式を括弧でくくったものは数式
  syntax:max "(" arith ")" : arith

  macro_rules
    | `([arith| $n:num]) => `(Arith.val $n)
    | `([arith| $l:arith + $r:arith]) => `(Arith.app Op.add [arith| $l] [arith| $r])
    | `([arith| $l:arith * $r:arith]) => `(Arith.app Op.mul [arith| $l] [arith| $r])
    | `([arith| ($e:arith)]) => `([arith| $e])

end Arith

open Lean Elab Term Syntax Qq

/-- Leanのパーサを利用して、文字列をパースして`Arith`を得る -/
unsafe def parseArith (input : String) : TermElabM Arith := do
  let env ← getEnv
  let stx ← Lean.ofExcept <| Parser.runParserCategory env `term s!"[arith| {input}]"
  let expr : Q(Arith) ← elabTerm stx q(Arith)
  let arith : Arith ← Meta.evalExpr Arith q(Arith) expr
  return arith

#eval show TermElabM Bool from do
  let expected := Arith.app Op.add (Arith.val 1) (Arith.val 2)
  let actual ← parseArith "1 + 2"
  return expected = actual
