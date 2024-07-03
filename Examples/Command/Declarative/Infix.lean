/- # infix
`infix` は，中置記法を定義する構文です．
-/
import Lean --#
namespace Infix --#

-- 中置記法を定義. 中身はただの掛け算
-- 特定の名前空間でだけ有効にするために `scoped` を付けている
scoped infix:60 " ⋄ " => Nat.mul

#guard 2 ⋄ 3 = 6

/- `:` の後に付けている数字はパースの優先順位で，高いほど結合するタイミングが早くなります．等号 `=` の優先順位は 50 であることを覚えておくと良いかもしれません．-/

-- 等号より微妙に優先順位が高い
scoped infix:51 " strong " => Nat.add

-- きちんと 1 + (2 strong 3) = 6 と解釈される．
-- これは， 等号の優先順位が 51 未満であることを意味する
#check 1 + 2 strong 3 = 6

-- 優先順位を 50 より小さくすると等号より優先順位が低くなる
-- したがってエラーになる
scoped infix:49 " weak " => Nat.add

#check_failure 1 + 2 weak 3 = 6

/- ## 舞台裏

`infix` は [`notation`](./Notation.md) コマンドの特別な場合であり，実際内部的にはマクロとして展開されます．以下の例では，`infix:50 " LXOR " => fun l r => (!l && r)` が `notation:50 lhs:51 " LXOR " rhs:51 => (fun l r => (!l && r)) lhs rhs` とマクロ展開されていることがわかります．-/

open Lean

/-- コマンドをマクロ展開するコマンド -/
elab "#expand_command " t:command : command => do
  match ← Elab.liftMacroM <| Lean.Macro.expandMacro? t with
  | none => logInfo m!"Not a macro"
  | some t =>
    logInfo m!"{t}"

/-- info: notation:50 lhs✝:51 " LXOR " rhs✝:51 => (fun l r => (!l && r)) lhs✝ rhs✝ -/
#guard_msgs in #expand_command infix:50 " LXOR " => fun l r => (!l && r)

end Infix --#