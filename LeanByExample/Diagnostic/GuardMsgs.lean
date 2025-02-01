/-
# \#guard_msgs

`#guard_msgs` コマンドは、あるコマンドの出力が与えられた文字列と一致するか検証します。
-/
import Mathlib.Algebra.Group.Defs -- 逆数を使うために必要 --#

/-- info: 2 -/
#guard_msgs in #eval 2

/--
error: failed to synthesize
  HAdd ℕ String String
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #eval (2 + "hello" : String)

/- ## 空白の違いを無視させるには
`#guard_msgs` コマンドは空白の数に敏感で、空白の長さによって通ったり通らなかったりします。しかし、`whitespace` という引数に `lax` を指定することにより、この空白に関する制限は緩めることができます。
-/

variable (α : Type)

-- 通常の場合
/--
error: failed to synthesize
  Inv α
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #check (_ : α)⁻¹

-- スペースを入れてもエラーにならない
/--
error:
  failed to synthesize
    Inv α
  Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (whitespace := lax) in #check (_ : α)⁻¹

/- ## 舞台裏

`#guard_msgs` コマンドは「与えられたコマンドを実行してその出力メッセージを取り出す」ということを行いますが、これは `elabCommandTopLevel` 関数で実行することができます。これを利用すると、`#guard_msgs` コマンドの派生コマンドを自分で定義することができます。

ここでは例として、「ドキュメントコメントに書かれた内容が出力メッセージに含まれるかどうか判定するコマンド」を定義してみます。
-/

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
    | `(command| $[$doc?:docComment]? #contain_msg in $cmd:command) => do
      -- 与えられたコマンドを実行する
      withReader ({ · with snap? := none }) do
        elabCommandTopLevel cmd

      -- コマンドの実行結果のメッセージを取得する
      let msgs := (← get).messages.toList
      let msgStrs := (← msgs.mapM (·.data.toString))
        |>.map (·.replace "\"" "")

      -- doc comment に書かれた文字列を取得する
      let expected? := (← doc?.mapM (getDocStringText ·))
      let some expected := expected?.map String.trim
        | logInfo "success: nothing is expected"

      -- コマンドの実行結果のメッセージに expected が含まれるか検証する
      for msgStr in msgStrs do
        unless String.substr msgStr expected do
          logError "error: output string does not contain the expected string"
end

/-- ello -/ #contain_msg in #eval "hello"

/-- error: error: output string does not contain the expected string -/
#guard_msgs (error) in
  /-- 21 -/ #contain_msg in #eval 23
