/-
次の目標は、列挙型に対して `instance` コマンドを自動生成することです。
以下のように実装することができます。
-/

import Lean

open Lean Elab Command
open Parser.Term

/-- 与えられた 列挙型を表す `declName : Name` に対して、
`ToString` のインスタンスを与える `instance` コマンドを自動生成する -/
def mkToStringInstForEnum (declName : Name) : TermElabM Command := do
  if !(← isEnumType declName) then
    throwError "{declName} は列挙型ではありません"

  let indVal ← getConstInfoInduct declName
  let mut alts : Array (TSyntax ``matchAlt) := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let ctorStr := ctorInfo.name.getString!
    let alt ← `(matchAltExpr| | $(mkIdent ctorName):ident => $(quote ctorStr))
    alts := alts.push alt

  let typeIdent := mkIdent declName
  let ToStringIdent := mkIdent `ToString
  `(command|
    instance : $ToStringIdent:ident $typeIdent:ident := ⟨
      fun x => match x with
      $alts:matchAlt*⟩)

/-
いま定義した、`instance` コマンドを生成する関数を具体的な列挙型に対して実行して、得られたコマンドを確認してみましょう。
実際に、好ましい `instance` コマンドが生成されていることが確認できます。
-/

inductive Direction where
  | north
  | south
  | east
  | west

/--
info: instance : ToString Direction :=
  ⟨fun x✝ =>
    match x✝ with
    | Direction.north => "north"
    | Direction.south => "south"
    | Direction.east => "east"
    | Direction.west => "west"⟩
-/
#guard_msgs in --#
run_cmd
  let cmd ← liftTermElabM <| mkToStringInstForEnum `Direction
  let fmt ← liftCoreM <| PrettyPrinter.ppCommand cmd
  logInfo <| MessageData.ofFormat fmt

/-
得られたコマンドを `elabCommand` 関数で実行してやることで、`Direction` に対する `ToString` インスタンスが自動生成できることも確認できます。
-/

-- 実際にコマンドを実行して、`ToString` インスタンスを生成する
run_cmd
  let cmd ← liftTermElabM <| mkToStringInstForEnum `Direction
  elabCommand cmd

#guard toString Direction.north = "north"
#guard toString Direction.south = "south"
