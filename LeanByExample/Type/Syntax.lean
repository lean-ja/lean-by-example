/- # Syntax

`Lean.Syntax` は、Lean の具象構文木(concrete syntax tree)を表すデータ型です。

具象構文木とは何かを理解するには、私たちがエディタに `#eval "Hello"` などと入力したとき、Lean がこれを実行する過程で何をしているかを考えるとわかりやすいでしょう。入力された `#eval "Hello"` は最初は単なる文字列ですが、Lean はまずこれを Lean の文法に照らして合法的なコードであるか解析します。合法ならば次のステップに進むことができますし、そうでなければ「こんなコマンドは知らない」というエラーを表示します。この解析結果を保存する中間的データが具象構文木(`Syntax`)として表現されます。

なお、ただの文字列を解析して構文木を得ることを構文解析または **パース(parse)** と呼びます。

## 定義

`Syntax` 型は以下のように[帰納型](#{root}/Declarative/Inductive.md)として定義されています。
-/
import Lean --#
namespace Hidden --#

open Lean

/-- 構文木 -/
inductive Syntax where
  /-- パース時のエラー。エラーが起こったときにそれ以降のパースが
  すべて失敗するということを避けるために用意されている。-/
  | missing : Syntax

  /-- 構文木のノード -/
  | node (info : SourceInfo) (kind : SyntaxNodeKind) (args : Array Syntax) : Syntax

  /-- アトム(`atom`)は、構文木の葉の部分を構成する。
  `⊕` や `+` などの演算子、`(` や `)` などの括弧がこれにあたる。-/
  | atom (info : SourceInfo) (val : String) : Syntax

  /-- 識別子(`ident`)は、構文木の葉の部分を構成する。たとえば以下は識別子である。
  * `Nat.add` などの関数名
  * 式 `1 + x` における変数名 `x`
  -/
  | ident (info : SourceInfo) (rawVal : Substring)
    (val : Name) (preresolved : List Syntax.Preresolved) : Syntax

--#--
-- Syntax の定義の変更を確認するためのコード
/--
info: inductive Lean.Syntax : Type
number of parameters: 0
constructors:
Lean.Syntax.missing : Lean.Syntax
Lean.Syntax.node : SourceInfo → SyntaxNodeKind → Array Lean.Syntax → Lean.Syntax
Lean.Syntax.atom : SourceInfo → String → Lean.Syntax
Lean.Syntax.ident : SourceInfo → Substring → Name → List Syntax.Preresolved → Lean.Syntax
-/
#guard_msgs in #print _root_.Lean.Syntax
--#--
end Hidden --#

/- ## パースと構文木
実際に、`s : String` を解析して `Syntax` の項を得ることができます。-/

open Lean Parser

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

-- `true` は識別子としてパースされている。
/--
info: Lean.Syntax.ident
  (Lean.SourceInfo.original "".toSubstring { byteIdx := 0 } "".toSubstring { byteIdx := 4 })
  "true".toSubstring
  `true
  []
-/
#guard_msgs in
  #eval parse `term "true"

-- `0` は構文木のノードになっていて、
-- 子としてアトムが一つある。
/--
info: Lean.Syntax.node
  (Lean.SourceInfo.none)
  `num
  #[Lean.Syntax.atom (Lean.SourceInfo.original "".toSubstring { byteIdx := 0 } "".toSubstring { byteIdx := 1 }) "0"]
-/
#guard_msgs in
  #eval parse `term "0"

/- 見ての通りすぐに複雑怪奇になってしまうので、以降は表示を簡略化しましょう。`Syntax` は [`ToString`](#{root}/TypeClass/ToString.md) のインスタンスを実装しており、これは `SourceInfo` などを含まないシンプルな表現をしてくれるので、それを利用します。-/

-- 文字列として表示するとかなり簡略化される
/-- info: `true -/
#guard_msgs in
  run_meta IO.println (← parse `term "true")

/-- info: (num "0") -/
#guard_msgs in
  run_meta IO.println (← parse `term "0")

/-- info: (term!_ "!" `false) -/
#guard_msgs in
  run_meta IO.println (← parse `term "! false")

-- 識別子はアトムと違って `Name` を受け取るのでバッククォートがつく
/-- info: `Nat.zero -/
#guard_msgs in
  run_meta IO.println (← parse `term "Nat.zero")

/- もちろん項(`term`)以外の構文カテゴリについてもパースを行うことができます。あと少しだけ例を見ましょう。 -/

-- コマンドをパースする例
/-- info: (Command.eval "#eval" (str "\"hello\"")) -/
#guard_msgs in
  run_meta IO.println (← parse `command "#eval \"hello\"")

-- タクティクをパースする例
-- 木構造が現れている
/--
info: (Tactic.«tactic_<;>_» (Tactic.constructor "constructor") "<;>" (Tactic.intro "intro" [`h]))
-/
#guard_msgs in
  run_meta IO.println (← parse `tactic "constructor <;> intro h")
