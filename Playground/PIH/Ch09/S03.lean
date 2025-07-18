import Playground.PIH.Ch09.S02

/-- 途中に現れる可能性のある数式 -/
inductive Expr where
  /-- 数値リテラル -/
  | val : Pos → Expr
  /-- 演算子の適用 -/
  | app : Op → Expr → Expr → Expr

namespace Expr
  /- ## Expr の項を定義するための簡単な構文を用意する -/

  /-- `Expr` のための構文カテゴリ -/
  declare_syntax_cat expr

  /-- `Expr` を見やすく定義するための構文 -/
  syntax "expr!{" expr "}" : term

  -- 一時的にリンターをOFFにする
  set_option linter.missingDocs false

  syntax:max num : expr
  syntax:30 expr:30 " + " expr:31 : expr
  syntax:30 expr:30 " - " expr:30 : expr
  syntax:35 expr:35 " * " expr:36 : expr
  syntax:37 expr:37 " / " expr:37 : expr
  syntax:max "(" expr ")" : expr

  macro_rules
    | `(expr!{$n:num}) => `(Expr.val $n)
    | `(expr!{$l:expr + $r:expr}) => `(Expr.app Op.add expr!{$l} expr!{$r})
    | `(expr!{$l:expr - $r:expr}) => `(Expr.app Op.sub expr!{$l} expr!{$r})
    | `(expr!{$l:expr * $r:expr}) => `(Expr.app Op.mul expr!{$l} expr!{$r})
    | `(expr!{$l:expr / $r:expr}) => `(Expr.app Op.div expr!{$l} expr!{$r})
    | `(expr!{($e:expr)}) => `(expr!{$e})

  -- 足し算は左結合になる
  /-- info: app Op.add (app Op.add (val 1) (val 2)) (val 3) : Expr -/
  #guard_msgs in
    #check expr!{1 + 2 + 3}

  -- 掛け算は左結合になる
  /-- info: app Op.mul (app Op.mul (val 1) (val 2)) (val 3) : Expr -/
  #guard_msgs in
    #check expr!{1 * 2 * 3}

  -- 足し算と掛け算が混在する場合は、掛け算が優先される
  /-- info: app Op.add (app Op.mul (val 1) (val 2)) (val 3) : Expr -/
  #guard_msgs in
    #check expr!{1 * 2 + 3}
end Expr

namespace Expr
  /- ## ToString インスタンスを定義する -/

  private def toString : Expr → String
    | Expr.val x => ToString.toString x
    | Expr.app op l r =>
      brak l ++ ToString.toString op ++ brak r
  where
    brak : Expr → String
    | .val n => ToString.toString n
    | e => "(" ++ toString e ++ ")"

  instance : ToString Expr := ⟨Expr.toString⟩

  -- toString インスタンスのテスト
  #guard toString expr!{1 + 2 * 3} = "1+(2*3)"
  #guard toString expr!{1 + (2 + 3 * 4)} = "1+(2+(3*4))"
  #guard toString expr!{(1 + 3) / 2} = "(1+3)/2"

  /- ## Repr インスタンスを定義する -/

  instance : Repr Expr where
    reprPrec e _ := s!"expr!\{{toString e}}"

  -- Repr インスタンスのテスト
  /-- info: expr!{1+(2*3)} -/
  #guard_msgs in
    #eval expr!{1 + 2 * 3}
end Expr

/-- 式の中に含まれる数値をリストにして返す -/
def Expr.values : Expr → List Pos
  | .val x => [x]
  | .app _ l r => l.values ++ r.values

/-- 式全体の値を評価する。途中で値が `Pos` にならなくなると、失敗する。 -/
def Expr.eval : Expr → Option Pos
  | .val x => x
  | .app op l r => do
    let x ← l.eval
    let y ← r.eval
    if h : op.valid x y then
      op.vapply x y
    else
      none
