/- # prefix

`prefix` は、前置記法を定義するためのコマンドです。
-/
import Lean --#
namespace Prefix --#

-- 前置記法を定義
-- 中身は Nat.succ
-- scoped を付けているのは、この記法をこの名前空間でのみ有効にするため
scoped prefix:90 "⋄" => Nat.succ

-- 上で定義した記法が使える
#guard ⋄3 = 4

/- ## 舞台裏
`prefix` は [`notation`](./Notation.md) コマンドに展開されるマクロとして実装されています。
-/

/-- `#expand` の入力に渡すための構文カテゴリ -/
syntax macro_stx := command <|> tactic <|> term

open Lean in

/-- マクロを展開するコマンド -/
elab "#expand " t:macro_stx : command => do
  let t : Syntax :=
    match t.raw with
    | .node _ _ #[t] => t
    | _ => t.raw
  match ← Elab.liftMacroM <| Macro.expandMacro? t with
  | none => logInfo m!"Not a macro"
  | some t => logInfo m!"{t}"

/-- info: notation:90 "⋄" arg✝:90 => Nat.succ arg✝ -/
#guard_msgs in
  #expand prefix:90 "⋄" => Nat.succ

end Prefix --#
