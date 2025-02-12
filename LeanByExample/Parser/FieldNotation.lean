/- # フィールド記法

**フィールド記法(field notation)** とは、大雑把に言えば `T` が `e` の型であるときに、関数適用 `T.f e` を `e.f` と書き表せるという記法のことです。あたかも `f` が `e` のフィールドであるかのように見えるのでこの名前があります。

典型的な例は、構造体 `S` の項 `e : S` に対して、構造体のフィールドのアクセサ関数 `S.f` の適用を `e.f` と書けることです。
-/
import Lean --#

structure Foo where
  x : Nat
  y : String

/-- Foo の項 -/
def bar : Foo := { x := 0, y := "" }

-- Foo のフィールドのアクセサ関数
#check Foo.x
#check Foo.y

-- フィールド記法を使ってアクセスすることができる
#guard bar.x = Foo.x bar
#guard bar.y = Foo.y bar

/- より詳細な仕様が、パーサのドキュメントコメントに書かれています。 -/

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name ← liftCoreM do realizeGlobalConstNoOverload x
  if let some s ← findDocString? (← getEnv) name then
  logInfo m!"{s}"

/--
info: The *extended field notation* `e.f` is roughly short for `T.f e` where `T` is the type of `e`.
More precisely,
* if `e` is of a function type, `e.f` is translated to `Function.f (p := e)`
  where `p` is the first explicit parameter of function type
* if `e` is of a named type `T ...` and there is a declaration `T.f` (possibly from `export`),
  `e.f` is translated to `T.f (p := e)` where `p` is the first explicit parameter of type `T ...`
* otherwise, if `e` is of a structure type,
  the above is repeated for every base type of the structure.

The field index notation `e.i`, where `i` is a positive number,
is short for accessing the `i`-th field (1-indexed) of `e` if it is of a structure type.
-/
#guard_msgs in
  #doc Lean.Parser.Term.proj
