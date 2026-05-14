/- # Linter

`Lean.Elab.Command.Linter` は構文リンター(syntax linter)の本体です。

構文リンターとは何かというと、Lean のリンター（よくない書き方のコードを検出するツール）の分類名です。
Lean のリンターには次の２種類があります。

* 環境リンター(environment linter): 環境に登録された定義・定理・インスタンスなどを**あとから横断的に**検査するリンター。
  [`#lint`](#{root}/Diagnostic/Lint.md) コマンドや `lake lint` コマンドで実行することができる。
  たとえば「この定理は使っていない仮定を持っていないか」「このインスタンスは危険な簡約規則を作っていないか」のように、
  すでに環境に入った宣言を対象にまとめてチェックする。
* 構文リンター(syntax linter): コマンドを処理する**その場で**構文や展開結果を検査し、問題があれば即座に警告するリンター。
  `set_option` コマンドなどで有効化して使う。
  たとえば「この宣言は `Classical.choice` に依存している」のような警告を、
  対象の宣言を定義した行で表示できる。
  [`Lean.Elab.Command.Linter`](#{root}/Type/Linter.md) を構成することによって自作できる。

要するに、ざっくり言えば次のように使い分ける。

* CI やレビュー時に一括実行したい検査 → 環境リンター
* コーディング中にその場でフィードバックが欲しい検査 → 構文リンター

-/

/- ## 使用例

選択原理を証明の中で使用すると警告してくれるリンターを自作する例を紹介します。[^dc]
まず以下のように記述したファイルを作成します。

{{#include ./Linter/DetectClassical.md}}

このファイルを読み込むと、次のように使用できます。

{{#include ./Linter/DetectClassicalUse.md}}
-/

/- [^dc]: この例は Lean 公式の Zulip の restricting axioms というトピックにおける、[Damiano Testa さんの投稿](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms/near/501743343)を参考にしています。 -/
