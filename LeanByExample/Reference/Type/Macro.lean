/- # Macro

`Lean.Macro` 型の項は、マクロを表現しています。一般のプログラミング言語においてマクロとは構文を構文に変換することですが、Lean の `m : Macro` は、`Syntax → MacroM Syntax` という型の関数そのものです。

[`Syntax`](./Syntax.md) 型が Lean の構文木をダイレクトに表していたように、`Macro` 型は Lean のマクロをダイレクトに表しています。
-/
import Mathlib.Util.WhatsNew

open Lean in

/-- `Macro` とは、おおむね `Syntax` から `Syntax` への関数である -/
example : Macro = (Syntax → MacroM Syntax) := by rfl

/- ## Macro 型とマクロの関係

### Macro 型からマクロ

項 `m : Macro` を使ってマクロを定義するには、以下のように `[macro]` 属性を使用します。
-/
open Lean

/-- `zeroLit` という構文の定義 -/
syntax (name := zeroLitPar) "zeroLit" : term

/-- `zeroLit` という構文を展開するマクロ -/
def zeroLitExpand : Macro := fun stx =>
  -- `stx : Syntax` に対するパターンマッチで関数を定義できる
  match stx with
  | `(zeroLit) => `(0)
  | _ => Macro.throwUnsupported

-- まだマクロとして登録されていないのでエラーになる
/--
error: elaboration function for 'zeroLitPar' has not been implemented
  zeroLit
-/
#guard_msgs in #check zeroLit

-- マクロとして登録する
attribute [macro zeroLitPar] zeroLitExpand

-- マクロ展開されるので、0 に等しいという結果になる
#guard zeroLit = 0

/- ### macro コマンドから Macro 型

実際に、`macro` コマンドなどでマクロを定義したとき、それが `Macro` 型の項を生成していることを確かめることができます。`whatsnew` コマンドで、特定のコマンドの実行後に新たに生成された識別子の名前をリストアップすることができます。以下の出力の中に `Lean.Macro` 型の項があるはずです。-/

whatsnew in macro "oneLit" : term => `(1)
