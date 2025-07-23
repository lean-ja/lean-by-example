import Mathlib.Util.WhatsNew
import Batteries.Data.String.Matcher

open Lean Elab Command

/-- コマンドの実行結果のメッセージに特定の文字列が含まれるかどうか検証するコマンド -/
syntax (docComment)? "#contain_msg" "in" command : command

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
      unless String.containsSubstr msgStr expected do
        logError "error: output string does not contain the expected string"

-- `macro_rules` コマンドの `whatsnew` コマンドによる出力の中に、`Macro` 型の項が含まれている
/-- def _aux_LeanByExample_Type_Macro_WhatsNew___macroRules_ident_1 : Macro := -/
#contain_msg in whatsnew in
  macro_rules
  | `(zeroLit) => `(1)
