/- # CommandElab

`Lean.Elab.Command.CommandElab` は、コマンドの内部実装を表現しています。

`CommandElab` 型の項は、`Syntax → CommandElabM Unit` 型の関数です。
-/
import Lean

open Lean in

example : Lean.Elab.Command.CommandElab = (Syntax → Lean.Elab.Command.CommandElabM Unit) := rfl

/- ## CommandElab 型の関数からコマンドへ

[`[command_elab]`](#{root}/Attribute/CommandElab.md) 属性を利用することで、`CommandElab` 型の関数からコマンドを作ることができます。
-/

/-- 挨拶をするコマンド -/
syntax (name := helloCommand) "#hello" : command

open Lean Elab Command in

@[command_elab helloCommand]
def evalHello : CommandElab := fun _stx => do
  let msg := s!"Hello, Lean!"
  logInfo msg

/-⋆-//-- info: Hello, Lean! -/
#guard_msgs in --#
#hello

/- ### ドキュメントコメントを取得するコマンド

識別子のドキュメントコメントを取得して表示するコマンドを定義する例です。
-/

syntax (name := docCmdStx) "#doc " ident : command

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
@[command_elab docCmdStx]
def evalDocCmd : CommandElab := fun stx =>
  match stx with
  | `(command| #doc $x:ident) => do
    let name ← liftCoreM do realizeGlobalConstNoOverload x
    if let some s ← findDocString? (← getEnv) name then
      logInfo m!"{s}"
  | _ => throwUnsupportedSyntax

/-⋆-//--
info: Characters are Unicode [scalar values](http://www.unicode.org/glossary/#unicode_scalar_value).
-/
#guard_msgs in --#
#doc Char
