/- # infix
`infix` は，中置記法を定義するコマンドです．
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

/- `infix` で定義される記法は左結合でも右結合でもなく，必ず括弧が必要です．-/
section

open Lean Parser

/-- parse できるかどうかチェックする関数 -/
def checkParse (cat : Name) (s : String) : MetaM Unit := do
  if let .error s := runParserCategory (← getEnv) cat s then
    throwError s

-- 単に連結するとパース不可でエラーになる
/-- error: <input>:1:6: expected end of input -/
#guard_msgs in run_meta checkParse `term "1 ⋄ 2 ⋄ 3"

-- 括弧を付ければOK
run_meta checkParse `term "1 ⋄ (2 ⋄ 3)"

end
/- ## 舞台裏

`infix` は [`notation`](./Notation.md) コマンドに展開されるマクロとして実装されています．-/

open Lean

def lxor (l r : Bool) : Bool := !l && r

/-- コマンドをマクロ展開するコマンド -/
elab "#expand_command " t:command : command => do
  match ← Elab.liftMacroM <| Lean.Macro.expandMacro? t with
  | none => logInfo m!"Not a macro"
  | some t => logInfo m!"{t}"

/-- info: notation:50 lhs✝:51 " LXOR " rhs✝:51 => lxor lhs✝ rhs✝ -/
#guard_msgs in
#expand_command infix:50 " LXOR " => lxor

end Infix --#
