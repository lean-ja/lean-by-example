/- # Linter

`Lean.Elab.Command.Linter` は構文リンター(syntax linter)の本体です。

構文リンターとは何かというと、Lean のリンター（よくない書き方のコードを検出するツール）の分類名です。
Lean のリンターには次の２種類があります。

* 環境リンター(environment linter): 環境に登録された定義・定理・インスタンスなどを検査するリンター。
  [`#lint`](#{root}/Diagnostic/Lint.md) コマンドや `lake lint` コマンドで実行することができる。
* 構文リンター(syntax linter): ソースコードの構文を見て、良くない書き方をその場で警告するリンター。
  `set_option` コマンドなどで有効化して使う。
  [`Lean.Elab.Command.Linter`](#{root}/Type/Linter.md) を構成することによって自作できる。

-/

/- ## 使用例

選択原理を証明の中で使用すると警告してくれるリンターを自作する例を紹介します。[^dc]
まず以下のように記述したファイルを作成します。

{{#include ./Linter/DetectClassical.md}}

このファイルを読み込むと、次のように使用できます。

{{#include ./Linter/DetectClassicalUse.md}}
-/

/- [^dc]: この例は Lean 公式の Zulip の restricting axioms というトピックにおける、[Damiano Testa さんの投稿](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms/near/501743343)を参考にしています。 -/
