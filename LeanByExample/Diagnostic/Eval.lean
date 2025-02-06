import Lean.Elab.Command --#
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
式の評価を行うコマンドであるため、型や関数など、評価のしようがないものを与えるとエラーになります。-/

-- 型は評価できない
/-⋆-//-- error: cannot evaluate, types are not computationally relevant -/
#guard_msgs in --#
#eval Nat

-- 関数そのものも評価できない
/-⋆-//--
error: could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  Nat → Nat
-/
#guard_msgs in --#
#eval (fun x => x + 1)

/- 一般に、[`Repr`](#{root}/TypeClass/Repr.md) や [`ToString`](#{root}/TypeClass/ToString.md) および `ToExpr` のインスタンスでないような型の項は `#eval` に渡すことができません。-/
