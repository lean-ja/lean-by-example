/- # CommandElab

`Lean.Elab.Command.CommandElab` は、コマンドの内部実装を表現しています。

`CommandElab` 型の項は、`Syntax → CommandElabM Unit` 型の関数です。
-/
import Lean

open Lean Elab Command in

example : CommandElab = (Syntax → CommandElabM Unit) := rfl

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
