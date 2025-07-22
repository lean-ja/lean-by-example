/-! ## 7.1 IMP Commands
最小限の命令型言語を定義する。構文はシンプルだが、これは
* while ループ
* 代入文
* if 分岐
を含んでおりチューリング完全になる。
-/

/-- 変数（の名前）。
ここでは簡単のために、すべての文字列が変数として存在するものとする -/
abbrev Variable := String

/-- プログラムの状態。すべての変数の値を保持したもの。
ここでは簡単にするために、変数の値はすべて自然数だとしている。 -/
def State := Variable → Nat

/-- 考察対象の言語 のコマンド -/
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

/-- `x > y` が成り立つ間、`x := x - 1` という代入文を実行し続けるプログラム -/
def sillyLoop : Stmt :=
  whileDo (fun s => s "x" > s "y")
    (skip;; assign "x" (fun s => s "x" - 1))

set_option quotPrecheck false in

/-- 状態 `s : State` があったとき、変数 `x` に対してだけ値を更新したものを表す記法 -/
notation s:70 "[" x:70 "↦" n:70 "]" => (fun v ↦ if v = x then n else s v)
