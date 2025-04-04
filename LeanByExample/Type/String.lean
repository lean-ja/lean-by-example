/- # String

`String` は文字列を表す型です。次のように、文字を表す型 [`Char`](#{root}/Type/Char.md) のリストとして定義されています。
-/
import Lean --#
--#--
-- String の定義が変わっていないことを確認するためのコード

/--
info: structure String : Type
number of parameters: 0
fields:
  String.data : List Char
constructor:
  String.mk (data : List Char) : String
-/
#guard_msgs in #print String
--#--
namespace Hidden --#

/-- 文字列 -/
structure String where
  /-- 文字列をほどいて `List Char` にする -/
  data : List Char

end Hidden --#

/- ## 文字列結合
`String.append` を使って文字列を結合することができます。この関数は `++` という記号が割り当てられています。
-/

#guard String.append "Hello, " "world!" = "Hello, world!"
#guard "Hello, " ++ "world!" = "Hello, world!"

/- ## 文字列の長さ
文字列の長さは `String.length` 関数で取得することができます。
-/

#guard "Hello".length = 5

#check List.length

/- `String.length` を素朴に実装すると、

1. 文字列を `List Char` に変換する
2. `List.length` を使って長さを求める

という手順になるかと思います。`n` 個の要素を持つ `xs : List α` に対して長さを求めようとすると、先頭から順に要素をたぐっていくので `n` に比例する時間がかかります。したがって `String.length` は長い文字列に対しては遅くなりそうなものですが、コンパイラによって実装がオーバーライドされているため、実際には `n` が大きくても高速に実行できます。

このあたりの背景はドキュメントコメントに書かれています。
-/

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name ← liftCoreM do realizeGlobalConstNoOverload x
  if let some s ← findDocString? (← getEnv) name then
  logInfo m!"{s}"

/--
info: A string is a sequence of Unicode code points.

At runtime, strings are represented by [dynamic arrays](https://en.wikipedia.org/wiki/Dynamic_array)
of bytes using the UTF-8 encoding. Both the size in bytes (`String.utf8ByteSize`) and in characters
(`String.length`) are cached and take constant time. Many operations on strings perform in-place
modifications when the reference to the string is unique.
-/
#guard_msgs in #doc String

/- ## 文字列補間

`String` 型の変数の「評価した後の値」を文字列に埋め込むことができます。これを **文字列補間(string interpolation)** と呼びます。Lean では、これは [`s!` という構文](#{root}/Parser/InterpStr.md)で行うことができます。
-/

def greet := "Hello"

/-⋆-//-- info: "Hello, world!" -/
#guard_msgs in --#
#eval s!"{greet}, world!"
