/- ## 8.7 抽象機械 -/

/-- 数式 -/
inductive Expr where
  /-- 自然数 -/
  | val (n : Nat)
  /-- 加算演算子 -/
  | add (left right : Expr)
deriving DecidableEq


namespace Expr
  /- ## Exprの項を表す構文を定義する -/

  /-- `Expr` のための構文カテゴリ -/
  declare_syntax_cat expr

  /-- `Expr` を見やすく定義するための構文 -/
  syntax "expr!{" expr "}" : term

  /-- 数値リテラルは数式 -/
  syntax:max num : expr

  /-- 数式を `+` で結合したものは数式-/
  syntax:30 expr:30 " + " expr:31 : expr

  /-- 数式を括弧でくくったものは数式 -/
  syntax:max "(" expr ")" : expr

  macro_rules
    | `(expr!{$n:num}) => `(Expr.val $n)
    | `(expr!{$l:expr + $r:expr}) => `(Expr.add expr!{$l} expr!{$r})
    | `(expr!{($e:expr)}) => `(expr!{$e})

  #guard
    let actual := expr!{(2 + 3) + 4}
    let expected := Expr.add (Expr.add (Expr.val 2) (Expr.val 3)) (Expr.val 4)
    actual = expected
end Expr


namespace Expr
  /- ## ExprのToStringインスタンスとReprインスタンスを構築する -/

  /-- 文字列変換 -/
  protected def toString : Expr → String
    | .val x => ToString.toString x
    | .add l r =>
      brak l ++ " + " ++ brak r
  where
    brak : Expr → String
    | .val n => ToString.toString n
    | e => "(" ++ Expr.toString e ++ ")"

  instance : ToString Expr := ⟨Expr.toString⟩

  #guard toString expr!{(2 + 3) + 4} = "(2 + 3) + 4"

  instance : Repr Expr where
    reprPrec e _ := "expr!{" ++ toString e ++ "}"

  /-- info: expr!{(2 + 3) + 4} -/
  #guard_msgs in #eval expr!{(2 + 3) + 4}
end Expr


namespace Hidden
  /- ## Exprの値を評価する

  `Expr.value`で値を評価すること自体はできるが、評価のステップを一つずつ進めるということができない。
  また、評価のステップを制御することができずLeanまかせになってしまう。(big step評価になる)
  -/

  /-- `Expr` の値を評価する関数(VMを使用しない) -/
  def value (e : Expr) : Nat :=
    match e with
    | .val n => n
    | .add l r => value l + value r

  #guard value expr!{(2 + 3) + 4} = 9
  #guard value expr!{1 + 1 + 1} = 3
end Hidden

section
  /- ## 制御スタック -/

  /-- 命令 -/
  inductive Op where
    /-- 式を評価せよという命令 -/
    | eval (e : Expr)
    /-- 数値を足せという命令 -/
    | add (n : Nat)

  @[inherit_doc] prefix:max "EVAL" => Op.eval
  @[inherit_doc] prefix:max "ADD" => Op.add

  /-- 制御スタック -/
  def Cont := List Op
end


namespace Op
  /- ## OpのToStringインスタンスとReprインスタンスを作る -/

  /-- 文字列に変換 -/
  protected def toString (op : Op) : String :=
    match op with
    | .eval e => s!"EVAL {e}"
    | .add n => s!"ADD {n}"

  instance : ToString Op := ⟨Op.toString⟩

  #guard (toString <| Op.eval expr!{42}) = "EVAL 42"

  instance : Repr Op where
    reprPrec op _ := repraux op
  where
    repraux (op : Op) : String :=
      match op with
      | .eval e => s!"EVAL {repr e}"
      | .add n => s!"ADD {n}"

  #eval EVAL expr!{42}
end Op

deriving instance ToString, Repr for Cont

mutual
  /- ## evalとexecの定義 -/

  /-- 制御スタック `c` にある命令に従って式 `e` を評価する -/
  partial def Cont.eval (e : Expr) (c : Cont) : Nat :=
    match e with
    /- 式が数値リテラルの場合は完全に評価済みなので、制御スタックの命令を実行する -/
    | .val n =>
      dbg_trace s!"exec {c} {n}"
      exec c n

    /- 式が加算演算子の場合は、最初の引数`l`を評価し、
    残りの引数`r`を評価するという命令を制御スタックに積む -/
    | .add l r =>
      dbg_trace f!"eval {repr l} (EVAL {r} :: {c})"
      eval l (EVAL r :: c)

  /-- 制御スタック `c` にある命令を現在値 `n` の下で実行する -/
  partial def Cont.exec (c : Cont) (n : Nat) : Nat :=
    match c with
    /- 制御スタックが空であれば、そのとき保持している現在値を結果として返す -/
    | [] =>
      dbg_trace n
      n

    /- 制御スタックの一番上が命令`Op.eval e`なら、
    `n`を足すのが式`e`が完全に評価された後になるように、命令`Add n`をスタックに積む -/
    | .eval e :: c =>
      dbg_trace f!"eval {repr e} (ADD {n} :: {c})"
      eval e (ADD n :: c)

    /- 制御スタックの一番上が命令`Add n`であれば、保持している値を単に更新する -/
    | .add m :: c =>
      dbg_trace s!"exec {c} {m + n}"
      exec c (m + n)
end

/-- 抽象機械を使って式の値を評価する -/
def Expr.value (e : Expr) : Nat := Cont.eval e []


/--
info: eval expr!{2 + 3} (EVAL 4 :: [])
eval expr!{2} (EVAL 3 :: [EVAL 4])
exec [EVAL 3, EVAL 4] 2
eval expr!{3} (ADD 2 :: [EVAL 4])
exec [ADD 2, EVAL 4] 3
exec [EVAL 4] 5
eval expr!{4} (ADD 5 :: [])
exec [ADD 5] 4
exec [] 9
9
---
info: 9
-/
#guard_msgs in
  #eval Expr.value expr!{(2 + 3) + 4}
