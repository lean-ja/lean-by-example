/- # Linter

`Lean.Elab.Command.Linter` は構文リンター(syntax linter)の本体です。

構文リンターとは何かというと、Lean のリンター（よくない書き方のコードを検出するツール）の分類名です。
Lean のリンターには次の２種類があります。

* 環境リンター(environment linter): 環境に登録された定義・定理・インスタンスなどを検査するリンター。
  [`#lint`](#{root}/Diagnostic/Lint.md) コマンドや `lake lint` コマンドで実行することができる。
* 構文リンター(syntax linter): 各コマンドのエラボレーション（Lean がコードを処理するフェーズ）のたびに自動的に実行されるリンター。
  `set_option` コマンドで個別に有効化・無効化することができる。
  [`Lean.Elab.Command.Linter`](#{root}/Type/Linter.md) を構成することによって自作できる。

「構文リンター」という名前は、リンターが `Syntax` 型の値（コードの構文木）を入力として受け取ることに由来します。
ただし、チェックの内容が必ずしも「構文的」なものに限らず、環境に登録された情報（公理への依存関係など）を参照することもあります。
環境リンターとの違いは「チェックする内容」ではなく「実行タイミングと方法」にあります。

-/

/- ## 使用例

選択原理（`Classical.choice`）に依存する宣言に対して警告してくれるリンターを自作する例を紹介します。[^dc]
まず以下のように記述したファイルを作成します。

{{#include ./Linter/DetectClassical.md}}

このファイルを読み込むと、次のように使用できます。

{{#include ./Linter/DetectClassicalUse.md}}

このリンターは公理への依存関係を調べるもので、「構文的」なチェックではありません。
しかし、`addLinter` で登録され各コマンドのエラボレーション時に実行されるため、構文リンターに分類されます。
-/

/- [^dc]: この例は Lean 公式の Zulip の restricting axioms というトピックにおける、[Damiano Testa さんの投稿](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms/near/501743343)を参考にしています。 -/
