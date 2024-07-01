/- # \#eval
`#eval` コマンドは，式の値を評価します．
-/
import Mathlib.Tactic --#

namespace eval --#

/-- info: 2 -/
#guard_msgs in #eval 1 + 1

-- 実行している Lean のバージョンが表示される
#eval Lean.versionString

def w := "world"

-- 文字列が代入されて "hello, world" と表示される
/-- info: "hello, world" -/
#guard_msgs in #eval s!"hello, {w}"

/-! 定義した関数が特定の値に対してどのように振る舞うか，その場で調べることができます．-/

-- 階乗関数
def fac : ℕ → ℕ
| 0 => 1
| n + 1 => (n + 1) * fac n

/-- info: 120 -/
#guard_msgs in #eval fac 5

/-! `#eval` により一部の IO アクションを実行することもできます．-/

def main : IO Unit :=
  IO.println "Hello, world!"

/-- info: Hello, world! -/
#guard_msgs in #eval main

/-! ## 例外処理の慣例
Lean および Mathlib では，「関数ではなく定理に制約を付ける」ことが慣例です．
関数の定義域を制限するアプローチだと，
関数を呼び出すたびに，引数が定義域に含まれているか確認する必要が生じて，
面倒になってしまうためです．
-/

-- たとえば，`1 / 0 = 0` となる．
-- ご存じのようにゼロで割るのは除算として定義できないのだが，
-- 除算の定義域を制限する代わりに，`1 / 0 = 0` という出力を割り当てている．
/-- info: 0 -/
#guard_msgs in #eval 1 / 0

-- もちろん，これは `0` であり `1` ではない．
/-- info: 0 -/
#guard_msgs in #eval (1 / 0) * 0

-- 他にも，自然数の引き算は，マイナスの代わりに `0` を返す．
/-- info: 0 -/
#guard_msgs in #eval 1 - 2

-- `1` ではなくて `2` になる．
/-- info: 2 -/
#guard_msgs in #eval (1 - 2) + 2

end eval --#
