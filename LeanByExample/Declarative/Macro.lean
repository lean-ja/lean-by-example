/- # macro

`macro` は、その名の通りマクロを定義するための簡便なコマンドです。ただし[マクロ](#{root}/Type/Macro.md)とは、構文を受け取って新しい構文を返す関数のことです。
-/
import Mathlib.Data.Real.Sqrt --#

open Lean Parser in

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

-- 最初は `#greet` が未定義なので、合法的なLeanのコマンドとして認識されない
/-- error: <input>:1:0: expected command -/
#guard_msgs in
  #eval parse `command "#greet"

-- `#greet` コマンドを定義する
macro "#greet " : command => `(#eval "Hello World!")

-- `#greet` コマンドが使用可能になった
#greet

/- ## 引数を取るマクロの例
冒頭の例の `#greet` コマンドは引数を持ちませんが、引数を取るようなものも定義できます。-/

-- 引数を取って、引数に対して挨拶するコマンドを定義する
-- 引数は `$` を付けると展開できる
macro "#hello " id:term : command => `(#eval s!"Hello, {$id}!")

/-- info: "Hello, Lean!" -/
#guard_msgs in #hello "Lean"

/- ## マクロによるタクティク作例
`macro` コマンドを使用すると、コマンドだけでなくタクティクの定義も行うことができます。-/

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
