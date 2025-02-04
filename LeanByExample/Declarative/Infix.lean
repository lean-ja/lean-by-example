/- # infix

`infix` は、中置記法を定義するコマンドです。
-/
import Lean --#

-- 中置記法を定義。中身はただの掛け算
infix:60 " ⋄ " => Nat.mul

#guard 2 ⋄ 3 = 6

/- `:` の後に付けている数字は **パース優先順位(parsing precedence)** で、高いほど結合するタイミングが早くなります。等号 `=` のパース優先順位は 50 であることを覚えておくと良いかもしれません。-/

-- 等号より微妙にパース優先順位が高い
infix:51 " strong " => Nat.add

-- きちんと 1 + (2 strong 3) = 6 と解釈される。
-- これは、 等号のパース優先順位が 51 未満であることを意味する
#check 1 + 2 strong 3 = 6

-- パース優先順位を 50 より低くすると等号より低くなる
-- したがってエラーになる
infix:49 " weak " => Nat.add

#check_failure 1 + 2 weak 3 = 6

/- `infix` で定義される記法は左結合でも右結合でもなく、必ず括弧が必要です。-/

open Lean Parser in

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

-- 単に連結するとパース不可でエラーになる
/-- error: <input>:1:6: expected end of input -/
#guard_msgs in #eval parse `term "1 ⋄ 2 ⋄ 3"

-- 括弧を付ければOK
#eval parse `term "1 ⋄ (2 ⋄ 3)"

/- ## 舞台裏

`infix` は [`notation`](./Notation.md) コマンドに展開されるマクロとして実装されています。-/

def lxor (l r : Bool) : Bool := !l && r

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

/-- info: notation:50 lhs✝:51 " LXOR " rhs✝:51 => lxor lhs✝ rhs✝ -/
#guard_msgs in
  #expand infix:50 " LXOR " => lxor
