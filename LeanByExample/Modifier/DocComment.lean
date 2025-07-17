import Lean --#
/- # ドキュメントコメント

Lean では、`/--` と `-/` で囲まれた部分がドキュメントコメントとして扱われます。

ドキュメントコメントをはじめコメントは、実行内容を持たないのでコードのプログラムとしての動作には影響しませんが、コードをわかりやすくするのに役立ちます。中でもドキュメントコメントは、直後に来る関数や定義を修飾して、そこに書かれた内容がマウスオーバーしたときに表示されるようになります。-/

/-- 階乗関数 -/
def Nat.factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * Nat.factorial n

/-
## ドキュメントコメントを扱う例

ドキュメントコメントは実行内容を持たないもののパースはされるので、コードの中で扱うことができます。

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
