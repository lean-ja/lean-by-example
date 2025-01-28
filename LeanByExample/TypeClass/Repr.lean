/-
# Repr
`Repr` は、その型の項をどのように表示するかを指示する型クラスです。

たとえば、以下のように新しく[構造体](#{root}/Declarative/Structure.md) `Point` を定義したとき、何も指定しなくても `Point` の項を `#eval` で表示することはできますが、実は裏で `Repr` インスタンスを利用しています。
-/
import Lean --#

-- 平面上の点を表す構造体
structure Point (α : Type) : Type where
  x : α
  y : α

-- 原点
def origin : Point Nat := ⟨0, 0⟩

-- `origin` の中身を表示することができる
/-- info: { x := 0, y := 0 } -/
#guard_msgs in #eval origin

-- Repr インスタンスを暗黙的に生成しないように設定
set_option eval.derive.repr false

-- 表示できずにエラーになった！
/--
error: could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  Point Nat
-/
#guard_msgs in #eval origin

/- ## Repr が満たすべきルール

`Repr` の出力は Lean のコードとしてパース可能なものに可能な限り近くなければならない、つまり Lean のコードとして実行可能であることが期待されます。このルールは `Repr` のドキュメントコメントに書かれています。
-/

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name ← liftCoreM do realizeGlobalConstNoOverload x
  if let some s ← findDocString? (← getEnv) name then
  logInfo m!"{s}"

/--
info: A typeclass that specifies the standard way of turning values of some type into `Format`.

When rendered this `Format` should be as close as possible to something that can be parsed as the
input value.
-/
#guard_msgs in #doc Repr

/- ## Repr インスタンスの実装方法

`Repr` 型クラスの定義は次のようになっています。-/

--#--
-- ## Repr の定義を確認するためのコード
/--
info: class Repr.{u} (α : Type u) : Type u
number of parameters: 1
fields:
  Repr.reprPrec : α → Nat → Std.Format
constructor:
  Repr.mk.{u} {α : Type u} (reprPrec : α → Nat → Std.Format) : Repr α
-/
#guard_msgs in #print Repr
--#--
namespace Hidden --#

class Repr.{u} (α : Type u) where
  /--
  `α` 型の項を、与えられた優先度で `Format` に変換する。
  優先度は、括弧を付けるかどうかの判断に使用される。
  -/
  reprPrec : α → Nat → Std.Format

end Hidden --#
/- したがって `Repr` のインスタンスを実装するには `Std.Format` の項を構成する必要がありそうですが、実は必ずしもこれを明示的に構成する必要はありません。 -/

/- ### deriving を使う

[`deriving`](#{root}/Declarative/Deriving.md) コマンドで Lean に `Repr` インスタンスを自動生成させることができます。-/

deriving instance Repr for Point

/-- info: { x := 0, y := 0 } -/
#guard_msgs in #eval origin

/- あるいは、そもそも型を定義する際に [`deriving`](#{root}/Declarative/Deriving.md) 句を用いて生成しても良いでしょう。-/

structure Point' (α : Type) : Type where
  x : α
  y : α
deriving Repr

def origin' : Point' Nat := ⟨0, 0⟩

-- 評価できる
#eval origin'

/- なお `Repr` の実装が満たすべきルールとして「出力は実行可能な Lean のコードでなければならない」というものがあるので、自分で構文を用意しない限り `deriving` を使わずに `Repr` インスタンスを実装する機会はないはずです。 -/

/- ### ToString インスタンスから作る
[`ToString`](#{root}/TypeClass/ToString.md) クラスのインスタンスから、`Repr` のインスタンスを得ることができます。
-/

instance {α : Type} [ToString α] : Repr α where
  reprPrec x _ := toString x

/- 実装すべきメソッド `Repr.reprPrec` の型は `α → Nat → Std.Format` なので型が合わないようですが、上記のコードが通るのは `String` から `Format` への[型強制](#{root}/TypeClass/Coe.md)が存在するためです。-/

-- `String → Format` という型強制が存在する
#synth Coe String Std.Format

/- これを利用すると `Repr` の実装が手軽に得られます。

以下に紹介する例は少し長くて複雑ですが、[`macro_rules`](#{root}/Declarative/MacroRules.md) コマンドを使用して見やすい構文を用意した後、`Repr` の出力がその構文になるように `Repr` インスタンスを定義する例です。
-/

/-- 2項演算の集合 -/
inductive Op where
  /-- 加法 -/
  | add
  /-- 乗法 -/
  | mul
deriving BEq

namespace Op
  -- ## ToString インスタンスの定義

  protected def toString : Op → String
    | add => "+"
    | mul => "*"

  instance : ToString Op := ⟨Op.toString⟩

end Op

/-- 数式 -/
inductive Expr where
  /-- 数値リテラル -/
  | val : Nat → Expr
  /-- 演算子の適用 -/
  | app : Op → Expr → Expr → Expr
deriving BEq

namespace Expr
  -- ## Expr の項を定義するための見やすい構文を用意する

  /-- `Expr` のための構文カテゴリ -/
  declare_syntax_cat expr

  /-- `Expr` を見やすく定義するための構文 -/
  syntax "expr!{" expr "}" : term

  syntax:max num : expr
  syntax:30 expr:30 " + " expr:31 : expr
  syntax:35 expr:35 " * " expr:36 : expr
  syntax:max "(" expr ")" : expr

  macro_rules
    | `(expr!{$n:num}) => `(Expr.val $n)
    | `(expr!{$l:expr + $r:expr}) => `(Expr.app Op.add expr!{$l} expr!{$r})
    | `(expr!{$l:expr * $r:expr}) => `(Expr.app Op.mul expr!{$l} expr!{$r})
    | `(expr!{($e:expr)}) => `(expr!{$e})

  -- 構文が正しく動作しているかテスト
  #guard
    let expected := Expr.app Op.add (app Op.mul (val 1) (val 2)) (val 3)
    let actual := expr!{1 * 2 + 3}
    expected == actual
end Expr

namespace Expr
  -- ## ToString インスタンスを定義する

  protected def toString : Expr → String
    | Expr.val x => ToString.toString x
    | Expr.app op l r =>
      brak l ++ ToString.toString op ++ brak r
  where
    brak : Expr → String
    | .val n => ToString.toString n
    | e => "(" ++ Expr.toString e ++ ")"

  instance : ToString Expr := ⟨Expr.toString⟩

  -- toString インスタンスのテスト
  #guard toString expr!{1 + 2 * 3} = "1+(2*3)"
  #guard toString expr!{1 + (2 + 3 * 4)} = "1+(2+(3*4))"
end Expr

namespace Expr
  -- ## Repr インスタンスを定義する

  -- `ToString` インスタンスを利用して `Repr` インスタンスを実装する
  instance : Repr Expr where
    reprPrec e _ := "expr!{" ++ toString e ++ "}"

  -- Repr インスタンスのテスト
  /-- info: expr!{1+(2*3)} -/
  #guard_msgs in
    #eval expr!{1 + (2 * 3)}

end Expr
