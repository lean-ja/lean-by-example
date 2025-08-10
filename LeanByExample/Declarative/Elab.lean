/- # elab

`elab` コマンドは、構文とその解釈を同時に定義するためのコマンドです。マクロと似ていますが、マクロとは違ってコードの置換ではなく手続き的な処理に向いています。このコマンドを使うと、コマンドやタクティクや項エラボレータを手軽に定義することができます。

より詳しく書くと、`elab` コマンドは構文とそのエラボレータを同時に定義するためのコマンドです。ただしエラボレータとは、おおざっぱに言えば [`Syntax`](#{root}/Type/Syntax.md) を [`Expr`](#{root}/Type/Expr.md) に変換する処理のことです。

## 使用例

### タクティク

`elab` コマンドを使わずにタクティクを定義しようとすると、以下の手続きを踏む必要があります。

1. 構文を定義する。
2. [`Tactic`](#{root}/Type/Tactic.md) 型の関数を定義する。
3. 構文と実装を [`[tactic]`](#{root}/Attribute/Tactic.md) 属性で結びつける。
-/
import Lean

/-- 挨拶をするだけのタクティク -/
syntax (name := greetStx) "greet₁" : tactic

open Lean Elab Tactic in

@[tactic greetStx]
def evalGreet : Tactic := fun _ =>
  logInfo "Hello, world!"

/-⋆-//-- info: Hello, world! -/
#guard_msgs in --#
example : True := by
  greet₁
  trivial

/- `elab` コマンドを使用すると、これらを一括で行うことができます。 -/

open Lean Elab Tactic in

elab "greet₂" : tactic =>
  logInfo "Hello, world!"

/-⋆-//-- info: Hello, world! -/
#guard_msgs in --#
example : True := by
  greet₂
  trivial

/- ### コマンド

`elab` コマンドを使わずにコマンドを定義しようとすると、以下の手続きを踏む必要があります。

1. 構文を定義する。
2. [`CommandElab`](#{root}/Type/CommandElab.md) 型の関数を定義する。
3. 構文と実装を [`[command_elab]`](#{root}/Attribute/CommandElab.md) 属性で結びつける。
-/

/-- 挨拶をするだけのコマンド -/
syntax (name := greetCmdStx) "#greet₁" : command

open Lean Elab Command in

@[command_elab greetCmdStx]
def evalGreetCmd : CommandElab := fun _ =>
  logInfo "Hello, world!"

/-⋆-//-- info: Hello, world! -/
#guard_msgs in --#
#greet₁

/- `elab` コマンドを使用すると、これらを一括で行うことができます。 -/

open Lean Elab Command in

elab "#greet₂" : command =>
  logInfo "Hello, world!"

/-⋆-//-- info: Hello, world! -/
#guard_msgs in --#
#greet₂

/- ### 項エラボレータ

`elab` コマンドを使わずに項エラボレータを定義しようとすると、以下の手続きを踏む必要があります。

1. 構文を定義する。
2. `TermElab` 型の関数を定義する。
3. 構文と実装を `[term_elab]` 属性で結びつける。
-/

syntax (name := greetTermStx) "<<" "greet₁" ">>" : term

open Lean Elab Term in

@[term_elab greetTermStx]
def evalGreetTerm : TermElab := fun _ _ => do
  return (toExpr "hello world")

/-⋆-//-- info: "hello world" -/
#guard_msgs in --#
#eval << greet₁ >>

/- `elab` コマンドを使用すると、これらを一括で行うことができます。-/

open Lean Elab Term in

elab "<<" "greet₂" ">>" : term =>
  return (toExpr "hello world")

/-⋆-//-- info: "hello world" -/
#guard_msgs in --#
#eval << greet₂ >>
