/- # Linter

`Lean.Elab.Command.Linter` は構文リンター(syntax linter)の本体です。

構文リンターとは何かというと、Lean のリンター（よくない書き方のコードを検出するツール）の分類名です。
構文リンターは基本的には各コマンドのエラボレーション時に自動で実行されます。
構文リンターの種類によっては、`set_option` コマンドなどで有効化する必要があります。

Lean のリンターには他に、[環境リンター(environment linter)](#{root}/Diagnostic/Lint.md)があります。
-/

/- ## 使用例

選択原理を証明の中で使用すると警告してくれるリンターを自作する例を紹介します。[^dc]
まず以下のように記述したファイルを作成します。

{{#include ./Linter/DetectClassical.md}}

このファイルを読み込むと、次のように使用できます。

{{#include ./Linter/DetectClassicalUse.md}}
-/

/- [^dc]: この例は Lean 公式の Zulip の restricting axioms というトピックにおける、[Damiano Testa さんの投稿](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms/near/501743343)を参考にしています。 -/
