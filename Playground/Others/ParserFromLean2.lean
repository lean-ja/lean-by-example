import Lean.Parser

/-- A set of binary operations -/
inductive Op where
  /-- Addition -/
  | add
  /-- Multiplication -/
  | mul
deriving DecidableEq, Repr, Inhabited

/-- Arithmetic expressions -/
inductive Arith where
  /-- Numeric literal -/
  | val : Nat → Arith
  /-- Application of a binary operator -/
  | app : Op → Arith → Arith → Arith
deriving DecidableEq, Repr, Inhabited

open Lean Parser in
unsafe def parseArith : Parser :=
  arithParser 0
where
  num : Parser := Term.num
  add : TrailingParser := trailing_parser:30:30 " + " >> arithParser 31
  mul : TrailingParser := trailing_parser:35:35 " * " >> arithParser 36
  paren : Parser := leading_parser:maxPrec "(" >> arithParser 0 >> ")"

  arithParserFnCore : ParserFn :=
    prattParser `arith parsingTables .default (mkAntiquot "arith" `arith (isPseudoKind := true)).fn
  arithParser (prec : Nat) : Parser :=
    { fn := adaptCacheableContextFn ({ · with prec }) (withCacheFn `arith arithParserFnCore) }
  parsingTables : PrattParsingTables := {
    trailingParsers := []
    trailingTable := [(`«+», add, 30), (`«*», mul, 30)].foldl (fun map (a, b) => map.insert a b) {}
    leadingParsers := []
    leadingTable := [(`«$», num, maxPrec), (`num, num, maxPrec), (`«(», paren, maxPrec)].foldl (fun map (a, b) => map.insert a b) {}
  }

open Lean in
partial def elabArith : TSyntax `arith → Except String Arith
  | `(parseArith| $a:arith + $b:arith) => return .app .add (← elabArith a) (← elabArith b)
  | `(parseArith| $a:arith * $b:arith) => return .app .mul (← elabArith a) (← elabArith b)
  | `(parseArith| $n:num) => return .val n.getNat
  | `(parseArith| ($a:arith)) => elabArith a
  | _ => throw s!"unexpected syntax"

open Lean Parser in
instance : Insert Token TokenTable := ⟨fun a b => b.insert a a⟩
open Lean Parser in
instance : Singleton Token TokenTable := ⟨fun a => insert a ∅⟩

open Lean Parser in
def arithFromString (input : String) : Except String Arith :=
  unsafe let env : Environment := unsafeCast () -- we won't use it, right?
  let tokens : TokenTable := {"$", "(", ")", "+", "*"}
  let state := parseArith.fn.run
    (mkInputContext input "<input>")
    (ParserModuleContext.mk env {} .anonymous [])
    tokens
    (mkParserState input)
  if state.hasError then
    throw state.errorMsg.get!.toString
  else
    elabArith ⟨state.stxStack.back⟩

#eval arithFromString "(3 + 2) * 5"
