/- # command_elab

`[command_elab]` 属性は、コマンドの実装である [`CommandElab`](#{root}/Type/CommandElab.md) 型の関数とコマンドの構文を結び付け、コマンドとして動作するようにします。
-/
import Lean

open Lean Elab Command in

/-- 挨拶をするコマンド -/
syntax (name := helloCommand) "#hello" : command

open Lean Elab Command in

def evalHello : CommandElab := fun _stx => do
  let msg := s!"Hello, Lean!"
  logInfo msg

-- 実装がないので #hello コマンドはまだ使えない
/-⋆-//-- error: elaboration function for `helloCommand` has not been implemented -/
#guard_msgs in --#
#hello

-- 属性を使って実装と構文を紐づける
attribute [command_elab helloCommand] evalHello

-- コマンドが使えるようになった
/-⋆-//-- info: Hello, Lean! -/
#guard_msgs in --#
#hello
