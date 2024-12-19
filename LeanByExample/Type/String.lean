/- # String

`String` は文字列を表す型です。次のように、文字を表す型 [`Char`](./Char.md) のリストとして定義されています。
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

という手順になるかと思います。`n` 個の要素を持つ `xs : List α` に対して長さを求めようとすると、先頭から順に要素をたぐっていくので `Ω(n)` 時間がかかります。したがって `String.length` は長い文字列に対しては遅くなりそうなものですが、コンパイラによって実装がオーバーライドされているため実際には `O(1)` 時間で実行できます。

このあたりの背景はドキュメントコメントに書かれています。
-/

open Lean Elab.Command

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name ← liftCoreM do realizeGlobalConstNoOverload x
  if let some s ← findDocString? (← getEnv) name then
  logInfo m!"{s}"

/--
info: `String` is the type of (UTF-8 encoded) strings.

The compiler overrides the data representation of this type to a byte sequence,
and both `String.utf8ByteSize` and `String.length` are cached and O(1).
-/
#guard_msgs in #doc String

/- ## 文字列補完

`String` 型の変数の「評価した後の値」を文字列に埋め込むことができます。これを文字列補完と呼びます。Lean では、これは `s!` という構文で行うことができます。
-/

def greet := "Hello"

/-- info: "Hello, world!" -/
#guard_msgs in
  #eval s!"{greet}, world!"
