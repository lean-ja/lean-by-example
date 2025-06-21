/- # Macro

`Lean.Macro` 型の項は、マクロの内部実装を表現しています。一般のプログラミング言語においてマクロとは構文を構文に変換することを指す言葉で、必ずしも特定の型や項に対応する概念ではありませんが、Lean の `m : Macro` は、`Syntax → MacroM Syntax` という関数型そのものです。-/
import Mathlib.Util.WhatsNew --#

open Lean in

example : Macro = (Syntax → MacroM Syntax) := by rfl
/- [`Syntax`](./Syntax.md) 型が Lean の構文木をダイレクトに表していたように、`Macro` 型は Lean のマクロをダイレクトに表しています。
-/

/- ## Macro 型とマクロの関係

### Macro 型からマクロ

項 `m : Macro` を使ってマクロを定義するには、以下のように [`[macro]`](#{root}/Attribute/Macro.md) 属性を付与します。
-/
open Lean

/-- `zeroLit` という構文の定義 -/
syntax (name := zeroLitPar) "zeroLit" : term

/-- `zeroLit` という構文を展開するマクロ -/
def zeroLitExpand : Macro := fun stx =>
  match stx with
  | `(zeroLit) => `(0)
  | _ => Macro.throwUnsupported

-- まだマクロとして登録されていないのでエラーになる
#check_failure zeroLit

-- マクロとして登録する
attribute [macro zeroLitPar] zeroLitExpand

-- マクロ展開されるので、0 に等しいという結果になる
#guard zeroLit = 0

/- ### マクロから Macro 型

実際にマクロを定義する際は、[`notation`](#{root}/Declarative/Notation.md) コマンドや [`macro`](#{root}/Declarative/Macro.md) コマンド、[`macro_rules`](#{root}/Declarative/MacroRules.md) コマンドなどを使用するでしょう。こういったコマンドでマクロを定義したとき、それが裏で `Macro` 型の項を生成していることを確かめることができます。特定のコマンドの実行後に新たに生成された識別子の名前をリストアップすることができる、`whatsnew` コマンドを使えば可能です。-/

section
  open Lean Elab Command

  /-- コマンドの実行結果のメッセージに特定の文字列が含まれるかどうか検証するコマンド -/
  syntax (docComment)? "#contain_msg" "in" command : command

  /-- s に t が部分文字列として含まれる -/
  def String.substr (s t : String) : Bool := Id.run do
    if t.isEmpty then
      return true
    if t.length > s.length then
      return false
    return (s.replace t "").length < s.length

  elab_rules : command
    | `(command| #contain_msg in $_cmd:command) => do
      logInfo "success: nothing is expected"

    | `(command| $doc:docComment #contain_msg in $cmd:command) => do
      -- ドキュメントコメントに書かれた文字列を取得する
      let expected := String.trim (← getDocStringText doc)
      if expected.isEmpty then
        logInfo "success: nothing is expected"
        return

      -- 与えられたコマンドを実行する
      withReader ({ · with snap? := none }) do
        elabCommandTopLevel cmd

      -- コマンドの実行結果のメッセージを取得する
      let msgs := (← get).messages.toList
      let msgStrs := (← msgs.mapM (·.data.toString))
        |>.map (·.replace "\"" "")

      -- コマンドの実行結果のメッセージに expected が含まれるか検証する
      for msgStr in msgStrs do
        unless String.substr msgStr expected do
          logError "error: output string does not contain the expected string"
end

-- `macro_rules` コマンドの `whatsnew` コマンドによる出力の中に、`Macro` 型の項が含まれている
/-- unsafe def _aux_LeanByExample_Type_Macro___macroRules_zeroLitPar_1._cstage1 : Macro := -/
#contain_msg in
  whatsnew in
    macro_rules
    | `(zeroLit) => `(1)

/- ## マクロ展開を確認する方法

マクロがどのように展開されているか確かめるには、次で示すように `Macro.expandMacro?` 関数が利用できます。
-/

section
  open Lean

  /-- `#expand` の入力に渡すための構文カテゴリ -/
  syntax macro_stx := command <|> tactic <|> term

  /-- マクロを展開するコマンド -/
  elab "#expand " "(" stx:macro_stx ")" : command => do
    let t : Syntax :=
      match stx.raw with
      | .node _ _ #[t] => t
      | _ => stx.raw
    match ← Elab.liftMacroM <| Macro.expandMacro? t with
    | none => logInfo m!"Not a macro"
    | some t => logInfo m!"{t}"
end

/-⋆-//-- info: notation:50 lhs✝:51 " LXOR " rhs✝:51 => lxor lhs✝ rhs✝ -/
#guard_msgs in --#
#expand (infix:50 " LXOR " => lxor)
