/- # postfix
`postfix` は、後置記法を定義するコマンドです。
-/
import Lean --#
namespace Postfix --#

/-- 階乗 -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- 後置記法を定義する
-- scoped を付けたのは、この後置記法をこの名前空間内でのみ有効にするため
scoped postfix:200 "!" => factorial

-- 定義した記法が使える
#guard 5! = 120

/- ## 舞台裏
`postfix` は [`notation`](./Notation.md) コマンドに展開されるマクロとして実装されています。
-/

open Lean

/-- コマンドをマクロ展開するコマンド -/
elab "#expand_command " t:command : command => do
  match ← Elab.liftMacroM <| Lean.Macro.expandMacro? t with
  | none => logInfo m!"Not a macro"
  | some t => logInfo m!"{t}"

/-- info: notation:200 arg✝:200 "!" => factorial arg✝ -/
#guard_msgs in
  #expand_command postfix:200 "!" => factorial

end Postfix --#
