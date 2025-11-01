import Lean --#
/- # ドキュメントコメント

Lean では、`/--` と `-/` で囲まれた部分がドキュメントコメントとして扱われます。

ドキュメントコメントは、コードをわかりやすくするのに役立ちます。直後に来る関数や定義を修飾して、そこに書かれた内容がマウスオーバーしたときに表示されます。-/

/-- 階乗関数 -/
def Nat.factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * Nat.factorial n

/-
なお、「コメント」を「コードの動作に影響を与えない人間向けの説明文」と定義するのであれば、Lean のドキュメントコメントはコメントではありません。誤った場所にドキュメントコメントを配置するとエラーになります。

{{#include ./DocComment/ParseError.md}}
-/

/-
## ドキュメントコメントを扱う例

ドキュメントコメントは Lean に無視されるわけではなく、他の構文要素と同様にパースされます。したがって特にコードの中で扱うことができます。

たとえば、ドキュメントコメントを取得して内容を表示するコマンドを書くことができます。
-/

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name := x.getId
  if let some s ← findDocString? (← getEnv) name then
    logInfo m!"{s}"

/-⋆-//-- info: 階乗関数 -/
#guard_msgs in --#
#doc Nat.factorial

/- ## 補足：コメントはパースされている

なお、ドキュメントコメントに限らず、Lean のコメントはパーサに無視されません。ただ実行内容を持たず、コードの動作に影響を与えないだけです。
-/
section --#
open Lean Elab Command Parser

/-⋆-//--
info: def foo :
    -- ここにコメント
    /- ここにもコメント -/
    True :=
  trivial
-/
#guard_msgs in --#
run_cmd liftTermElabM do
  let s := "def foo : \n\
    -- ここにコメント\n\
    /- ここにもコメント -/\n\
    True := trivial"
  let cmd : Command := ⟨← ofExcept <| runParserCategory (← getEnv) `command s⟩
  logInfo (← PrettyPrinter.ppCommand cmd)

end --#
