import Lean.Elab.Command --#
import Mathlib.Tactic.Eval --#
/- # \#eval
`#eval` コマンドは、式の値をその場で評価します。
-/

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
error: could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  Nat → Nat
-/
#guard_msgs in --#
#eval (fun x => x + 1)

/- `Repr` インスタンスがあれば関数であっても `#eval` に渡すことができます。 -/

-- 最初はエラーになってしまう
/-⋆-//--
error: could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
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
-/

def bar := 1 + 1

def foo₁ := eval% bar

def foo₂ := bar

/-⋆-//--
info: def foo₁ : Nat :=
2
-/
#guard_msgs in --#
#print foo₁

/-⋆-//--
info: def foo₂ : Nat :=
bar
-/
#guard_msgs in --#
#print foo₂
