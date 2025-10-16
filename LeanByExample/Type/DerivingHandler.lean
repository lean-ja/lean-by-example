/- # DerivingHandler

`Lean.Elab.DerivingHandler` は、型クラスのインスタンスの自動生成を行うための関数の型で、`Array Name → CommandElabM Bool` という型と等しいものです。
-/
import Lean

open Lean Elab Command

example : DerivingHandler = (Array Name → CommandElabM Bool) := by
  rfl

/-
## deriving ハンドラの登録

[`deriving`](#{root}/Declarative/Deriving.md) コマンドを使用したときに、対応する `DerivingHandler` 型の関数が呼び出されます。

簡単な例として、任意の型から `Unit` への自明な関数を提供する `ToUnit` という型クラスを考えてみましょう。この型クラスが与える変換は自明なので、どんな型に対しても実装方法は「わかりきって」おり自動生成できそうです。

{{#include ./DerivingHandler/ToUnit.md}}
-/

/-
この型クラスに対して `deriving` コマンドが使えるようにするには、まず以下のように記述したファイルを作成し、deriving ハンドラを登録します。

{{#include ./DerivingHandler/Lib.md}}

そうすると、このファイルを `import` することで以下のように使用できるようになります。

{{#include ./DerivingHandler/Use.md}}
-/
