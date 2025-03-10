/- # macro

`macro` は、その名の通り[マクロ](#{root}/Type/Macro.md)を定義するためのコマンドです。ただし[マクロ](#{root}/Type/Macro.md)とは、構文を構文に変換する機能のことです。
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
macro "#greet " : command => `(command| #eval "Hello World!")

-- `#greet` コマンドが使用可能になった
/-⋆-//-- info: "Hello World!" -/
#guard_msgs in --#
#greet

/- ## 舞台裏
[`syntax`](#{root}/Declarative/Syntax.md) コマンドと[`macro_rules`](#{root}/Declarative/MacroRules.md) コマンドを使用すれば、`macro` コマンドと同様のことが実現できます。`macro_rules` コマンドと比較すると、`macro` コマンドはマクロのための構文と展開ルールを同時に定義しているところが異なります。
-/
namespace Macro

  scoped macro "#hello " : command => `(command| #eval "Hello Lean!")

  -- `#hello` コマンドが使用可能になった
  /-⋆-//-- info: "Hello Lean!" -/
  #guard_msgs in --#
  #hello

end Macro

namespace MacroRules

  -- 構文の定義
  scoped syntax "#hello " : command

  -- 構文は認識されるが、解釈方法が定義されていないのでエラーになる
  /-⋆-//-- error: elaboration function for 'MacroRules.«command#hello»' has not been implemented -/
  #guard_msgs in --#
  #hello

  scoped macro_rules
    | `(#hello) => `(command| #eval "Hello Lean!")

  -- `#hello` コマンドが使用可能になった
  /-⋆-//-- info: "Hello Lean!" -/
  #guard_msgs in --#
  #hello

end MacroRules

/- ## マクロ作例

マクロでどのようなことができるのかを理解するには、例を見るのが最高の近道です。以下に、`macro` コマンドでマクロを定義する例をいくつか示します。なお [`macro_rules`](#{root}/Declarative/MacroRules.md) コマンドを使用すれば、より複雑なマクロも定義できます。

### 引数を取るマクロ
冒頭の例の `#greet` コマンドは引数を持ちませんが、引数を取るようなものも定義できます。引数は `$` を付けることでマクロ内で展開することができます。-/

-- 引数を取って、引数に対して挨拶するコマンドを定義する
-- 引数は `$` を付けると展開できる
macro "#hello " id:term : command => `(command| #eval s!"Hello, {$id}!")

/-⋆-//-- info: "Hello, Lean!" -/
#guard_msgs in --#
#hello "Lean"

/- ### タクティクを自作する
マクロを使用すると、コマンドだけでなくタクティクの定義も行うことができます。-/

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
macro "norm_sqrt" : tactic => `(tactic| focus
    rw [Real.sqrt_eq_cases]
    try ring_nf
    norm_num
  )

-- 新しいタクティクにより一発で証明が終わるようになった！
example : √4 = 2 := by norm_sqrt
example : √18 = 3 * √ 2 := by norm_sqrt

/- ### do 構文を追加する

マクロで `do` 構文を追加することができます。
-/

/-- 自前で定義した累積代入構文 -/
macro x:ident " += " e:term : doElem => `(doElem| ($x) := ($x) + $e)

/-- 0からnまでの和 -/
def sum (n : Nat) : Nat := Id.run do
  let mut sum := 0
  for i in [0:n+1] do
    sum += i
  return sum

#guard sum 3 = 6
#guard sum 4 = 10

/- ### 引数の値ではなく名前を参照

[`Quote`](#{root}/TypeClass/Quote.md) と組み合わせることで、マクロ展開時に、マクロの引数として与えられた変数の値だけでなく名前も参照することができます。
-/

-- 通常の dbg_trace の挙動。
-- 与えられた式の値だけを返し、与えられた式が何だったかは教えてくれない
/-⋆-//-- info: 1 -/
#guard_msgs in --#
#eval
  let x := 1
  dbg_trace x
  return ()

/-- 与えられている変数の名前も出力するような `dbg_trace` の変種 -/
macro "dbg_trace!" x:ident body:term : term =>
  -- 与えられている引数 `x` の名前を取得する
  let ident := Lean.quote x.getId.toString
  `(term| dbg_trace s!"{$ident} = {$x}"; $body)

-- 与えられた変数の名前を出力するようになった！
/-⋆-//-- info: y = 1 -/
#guard_msgs in --#
#eval
  let y := 1
  dbg_trace! y
  return ()
