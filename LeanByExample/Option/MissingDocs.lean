/- # linter.missingDocs

`linter.missingDocs` オプションを有効にすると、[ドキュメントコメント](#{root}/Modifier/DocComment.md)が与えられていない定義に対して警告が表示されます。
-/

set_option linter.missingDocs true

/-⋆-//--
warning: missing doc string for public def hoge

Note: This linter can be disabled with `set_option linter.missingDocs false`
-/
#guard_msgs in --#
def hoge := 42

-- ドキュメントコメントを付与すると警告が消える
#guard_msgs in --#
/-- なにがしかのコメント -/
def foo := 11

/- なお [`private`](#{root}/Modifier/Private.md) とマークされた定義には警告が出ません。-/

#guard_msgs in --#
private def bar := 99

/- [`theorem`](#{root}/Declarative/Theorem.md) で宣言された定理や補題に対しても警告が出ません。 -/

#guard_msgs in --#
theorem foo_hoge : foo + hoge = 53 := by
  rfl

/- ## 補足

上記で述べたように `linter.missingDocs` オプションは `theorem` を無視しますが、[`Linter`](#{root}/Type/Linter.md) を自作することによって、`theorem` に対してドキュメントを要求するようなリンターを自作できます。

まず、以下のようなファイルを作成します。

{{#include ./MissingDocs/DocBlameThm.md}}

このファイルを読み込むと、次のように使用できます。

{{#include ./MissingDocs/DocBlameThmUse.md}}
-/
