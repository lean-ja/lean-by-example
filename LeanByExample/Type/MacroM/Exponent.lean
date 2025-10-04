open Lean Macro Parser

/-- 指数表記 -/
declare_syntax_cat exp
syntax "⁰" : exp
syntax "¹" : exp
syntax "²" : exp
syntax "³" : exp
syntax "⁴" : exp
syntax "⁵" : exp
syntax "⁶" : exp
syntax "⁷" : exp
syntax "⁸" : exp
syntax "⁹" : exp

-- ホワイトスペースなしで`exp`が１つ以上連続したときにマッチ
syntax term (noWs exp)+ : term
syntax term "⁻"(noWs exp)+ : term

-- `Inv`のために用意されている`⁻¹`という構文を上書きする
syntax term "⁻¹"(noWs exp)+ : term

def expToNat (stx : TSyntax `exp) : Nat :=
  match stx with
  | `(exp|⁰) => 0
  | `(exp|¹) => 1
  | `(exp|²) => 2
  | `(exp|³) => 3
  | `(exp|⁴) => 4
  | `(exp|⁵) => 5
  | `(exp|⁶) => 6
  | `(exp|⁷) => 7
  | `(exp|⁸) => 8
  | `(exp|⁹) => 9
  | _ => 0 -- 無効な構文の場合は0を返す

def expToSyntax (exp : Array (TSyntax `exp)) (litPrefix := 0) : MacroM (TSyntax `term) := do
  let digits := exp.map expToNat
  let exp := digits.foldl (fun acc x => 10 * acc + x) litPrefix
  return quote exp

macro_rules
  | `($lhs $[$exp]*) => do
    let stx ← expToSyntax exp
    `($lhs ^ $stx)
  | `($lhs ⁻$[$exp]*) => do
    let stx ← expToSyntax exp
    `($lhs ^ (Int.neg $stx))
  | `($lhs ⁻¹$[$exp]*) => do
    let stx ← expToSyntax exp (litPrefix := 1)
    `($lhs ^ (Int.neg $stx))

#guard (2 : Int)⁰ = 1
#guard 2³ = 8
#guard (2 : Rat)⁻¹⁰ = (1 : Rat) / 1024
