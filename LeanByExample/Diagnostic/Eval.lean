/- # \#eval
`#eval` コマンドは、式の値をその場で評価します。
-/
import Lean.Elab.Command -- `#eval` コマンドのフルパワーを引き出す

/-⋆-//-- info: 2 -/
#guard_msgs in --#
#eval 1 + 1

-- 階乗関数
def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

/-⋆-//-- info: 120 -/
#guard_msgs in --#
#eval fac 5

def main : IO Unit :=
  IO.println "Hello, world!"

/-⋆-//-- info: Hello, world! -/
#guard_msgs in --#
#eval main

/- `#eval` による出力結果は編集することができます。代表的な方法は、[`Repr`](#{root}/TypeClass/Repr.md) クラスのインスタンスを実装することです。 -/

/-- ユーザが持つ権限 -/
inductive Role where
  | admin
  | write
  | read

/-⋆-//-- info: Role.admin -/
#guard_msgs in --#
#eval Role.admin

-- `#eval` の結果を強制的に上書きする
instance : Repr Role where
  reprPrec := fun _role _ => "ほげほげ！"

/-⋆-//-- info: ほげほげ！ -/
#guard_msgs in --#
#eval Role.admin

/- ## よくあるエラー

### 計算不能

`not computationally relevant` というエラーになることがあります。-/

/-⋆-//-- error: cannot evaluate, types are not computationally relevant -/
#guard_msgs in --#
#eval Nat

/-⋆-//-- error: cannot evaluate, proofs are not computationally relevant -/
#guard_msgs in --#
#eval (rfl : 1 + 1 = 2)

/- これは、Lean の型や証明項は計算可能な解釈を持たないためです。 -/

/- ### 表示方法がわからない

一般に [`Repr`](#{root}/TypeClass/Repr.md) や [`ToString`](#{root}/TypeClass/ToString.md) および `ToExpr` のインスタンスでないような型の項は、表示方法がわからないので `#eval` に渡すことができません。
-/

/-⋆-//--
error: could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Nat → Nat
-/
#guard_msgs in --#
#eval (fun x => x + 1)

/- `Repr` インスタンスがあれば関数であっても `#eval` に渡すことができます。 -/

-- 最初はエラーになってしまう
/-⋆-//--
error: could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Unit → Nat
-/
#guard_msgs in --#
#eval (fun _ => 1 : Unit → Nat)

instance {α : Type} [Repr α] : ToString (Unit → α) where
  toString x := s!"fun (_ : Unit) => {reprStr (x ())}"

-- Repr インスタンスを定義する
instance {α : Type} [Repr α] : Repr (Unit → α) where
  reprPrec x _ := toString x

-- #eval に渡せるようになった！
/-⋆-//-- info: fun (_ : Unit) => 1 -/
#guard_msgs in --#
#eval (fun _ => 1 : Unit → Nat)

/- ## 補足: 式の評価結果を代入する

`#eval` コマンドは式を評価してその結果をユーザに表示しますが、「式の評価結果を別のコードに代入する」には `eval%` を使います。

{{#include ./Eval/EvalTermElab.md}}
-/
