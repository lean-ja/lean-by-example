/- # CommandElab

`Lean.Elab.Command.CommandElab` は、コマンドの内部実装を表現しています。

`CommandElab` 型の項は、`Syntax → CommandElabM Unit` 型の関数です。
-/
import Lean

open Lean Elab Command in

example : CommandElab = (Syntax → CommandElabM Unit) := rfl

/-
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

/- ## コマンド作例

以下に、`CommandElab` 型の関数からコマンドを作る例を示します。
-/
/- ### 型を確かめるコマンド

以下は、与えられた項と型が一致するかどうかを確かめるコマンドの例です。[^assert_type]

{{#include ./CommandElab/AssertType.md}}
-/

/- [^assert_type]: このコード例は、[Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/) を参考にしました。 -/
