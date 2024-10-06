/- # macro

[`🏷️メタプログラミング`](./?search=🏷メタプログラミング)

`macro` は、その名の通りマクロを定義するための簡便なコマンドです。ただしマクロとは、構文を受け取って新しい構文を返す関数のことです。
-/
import Mathlib.Data.Real.Sqrt
namespace Macro --#

open Lean Parser

/-- 構文が認識されるかどうかチェックする関数 -/
def checkParse (cat : Name) (s : String) : MetaM Unit := do
  if let .error s := runParserCategory (← getEnv) cat s then
    throwError s

-- 最初は `#greet` が未定義なので、合法的なLeanのコマンドとして認識されない
/-- error: <input>:1:0: expected command -/
#guard_msgs in
  run_meta checkParse `command "#greet"

-- `#greet` コマンドを定義する
scoped macro "#greet " : command => `(#eval "Hello World!")

-- `#greet` コマンドが使用可能になった
#greet

/- 上記の例の `#greet` コマンドは引数を持ちませんが、引数を取るようなものも定義できます。-/

-- 引数を取って、引数に対して挨拶するコマンドを定義する
-- 引数は `$` を付けると展開できる
scoped macro "#hello " id:term : command => `(#eval s!"Hello, {$id}!")

/-- info: "Hello, Lean!" -/
#guard_msgs in #hello "Lean"

/- `macro` コマンドを使用すると、コマンドだけでなくタクティクの定義も行うことができます。-/

-- 平方根の計算
example : √4 = 2 := by
  rw [Real.sqrt_eq_cases]
  norm_num

-- 平方根の簡約
example : √18 = 3 * √ 2 := by
  rw [Real.sqrt_eq_cases]
  ring_nf
  norm_num

-- 新たなタクティクを定義する
macro "norm_sqrt" : tactic => `(tactic| with_reducible
  rw [Real.sqrt_eq_cases]
  try ring_nf
  norm_num)

-- 新しいタクティクにより一発で証明が終わるようになった！
example : √4 = 2 := by norm_sqrt
example : √18 = 3 * √ 2 := by norm_sqrt

end Macro --#
