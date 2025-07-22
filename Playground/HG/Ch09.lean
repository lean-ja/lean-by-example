
/-- 変数（の名前）。
ここでは簡単のために、すべての文字列が変数として存在するものとする -/
abbrev Variable := String

/-- プログラムの状態。すべての変数の値を保持したもの。
ここでは簡単にするために、変数の値はすべて自然数だとしている。 -/
def State := Variable → Nat

/-- 考察対象の言語 のコマンド -/
@[grind]
inductive Stmt : Type where
  /-- 何もしないコマンド。else 部分がない if 文などを実現するために必要。 -/
  | skip : Stmt
  /-- `x := a` のような代入文。
  * 最初の引数 `v : Variable` は代入対象の変数を表す。
  * 2つめの引数 `a : State → Nat` は arithmetic expression を表していて、
    変数への値の割り当て（つまり `State`）が与えられるごとに何か値を返すものとされる。-/
  | assign : Variable → (State → Nat) → Stmt
  /-- 2つのコマンドを続けて実行する。`;;` で表される。 -/
  | seq : Stmt → Stmt → Stmt
  /-- if 文。`ifThenElse B S T` は、`B` が真のとき `S` を実行して `B` が偽のとき `T` を実行することに対応。-/
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  /-- while 文 -/
  | whileDo : (State → Prop) → Stmt → Stmt

@[inherit_doc] infix:60 ";; " => Stmt.seq

-- 短い名前でアクセスできるようにする
export Stmt (skip assign seq ifThenElse whileDo)

set_option quotPrecheck false in

/-- 状態 `s : State` があったとき、変数 `x` に対してだけ値を更新したものを表す記法 -/
notation s:70 "[" x:70 "↦" n:70 "]" => (fun v ↦ if v = x then n else s v)

/-- IMP言語の文を表す構文カテゴリ -/
declare_syntax_cat imp_stmt

/-- 代入文 -/
syntax ident ":=" term : imp_stmt

/-- スキップ文 -/
syntax "skip" : imp_stmt

/-- if文 -/
syntax "if" term "then" imp_stmt "else" imp_stmt : imp_stmt

/-- while文 -/
syntax "while" term "does" imp_stmt : imp_stmt

/-- 2つの文を続けて実行する -/
syntax imp_stmt ";; " imp_stmt : imp_stmt

/-- トップレベルで使うためのエントリーポイント構文 -/
syntax "[imp_stmt| " imp_stmt "]" : term

open Lean

macro_rules
  | `([imp_stmt| skip]) => `(Stmt.skip)
  | `([imp_stmt| $x:ident := $a:term]) => `(Stmt.assign $(quote x.getId.toString) (fun s => $a))
  | `([imp_stmt| $s1:imp_stmt ;; $s2:imp_stmt]) =>
    `(Stmt.seq [imp_stmt| $s1] [imp_stmt| $s2])
  | `([imp_stmt| if $cond:term then $s1:imp_stmt else $s2:imp_stmt]) =>
    `(Stmt.ifThenElse (fun s => $cond) [imp_stmt| $s1] [imp_stmt| $s2])
  | `([imp_stmt| while $cond:term does $body:imp_stmt]) =>
    `(Stmt.whileDo (fun s => $cond) [imp_stmt| $body])
