/- # \#eval
`#eval` コマンドは、式の値をその場で評価します。
-/
import Mathlib.Tactic --#
namespace Eval --#

/-- info: 2 -/
#guard_msgs in #eval 1 + 1

-- 階乗関数
def fac : ℕ → ℕ
| 0 => 1
| n + 1 => (n + 1) * fac n

/-- info: 120 -/
#guard_msgs in #eval fac 5

def main : IO Unit :=
  IO.println "Hello, world!"

-- `#eval` により一部の IO アクションを実行することもできる
/-- info: Hello, world! -/
#guard_msgs in #eval main

/- ## よくあるエラー
式の評価を行うコマンドであるため、型や関数など、評価のしようがないものを与えるとエラーになります。-/

-- 型は評価できない
/-- error: cannot evaluate, types are not computationally relevant -/
#guard_msgs in #eval Nat

-- 関数そのものも評価できない
/--
error: could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  ℕ → ℕ
-/
#guard_msgs in #eval (fun x => x + 1)

/- 一般に、[`Repr`](../TypeClass/Repr.md) や [`ToString`](../TypeClass/ToString.md) および `ToExpr` のインスタンスでないような型の項は `#eval` に渡すことができません。-/

/- ## 例外処理の慣例
Lean および Mathlib では、「関数ではなく定理に制約を付ける」ことが慣例です。
関数の定義域を制限するアプローチだと、
関数を呼び出すたびに、引数が定義域に含まれているか確認する必要が生じて、
面倒になってしまうためです。
-/

-- たとえば、`1 / 0 = 0` となる。
-- ご存じのようにゼロで割るのは除算として定義できないのだが、
-- 除算の定義域を制限する代わりに、`1 / 0 = 0` という出力を割り当てている。
/-- info: 0 -/
#guard_msgs in #eval 1 / 0

-- もちろん、これは `0` であり `1` ではない。
/-- info: 0 -/
#guard_msgs in #eval (1 / 0) * 0

-- 他にも、自然数の引き算は、マイナスの代わりに `0` を返す。
/-- info: 0 -/
#guard_msgs in #eval 1 - 2

-- `1` ではなくて `2` になる。
/-- info: 2 -/
#guard_msgs in #eval (1 - 2) + 2

end Eval --#
