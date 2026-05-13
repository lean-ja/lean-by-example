/- # Linter

`Lean.Elab.Command.Linter` は syntax linter を実装するための仕組みです。
syntax linter は、個々の command の `Syntax` や、その command の elaboration 中に得られる情報を見て警告を出します。
そのため「そのコードをどう書いたか」を検査するのに向いています。

[`#lint`](#{root}/Diagnostic/Lint.md) が実行する environment linter とは別物です。
environment linter は elaboration 後の environment に登録された宣言を検査し、「その宣言をライブラリに追加して大丈夫か」を確認します。

-/

/- ## 使用例

選択原理を証明の中で使用すると警告してくれるリンターを自作する例を紹介します。[^dc]
まず以下のように記述したファイルを作成します。

{{#include ./Linter/DetectClassical.md}}

このファイルを読み込むと、次のように使用できます。

{{#include ./Linter/DetectClassicalUse.md}}
-/

/- [^dc]: この例は Lean 公式の Zulip の restricting axioms というトピックにおける、[Damiano Testa さんの投稿](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms/near/501743343)を参考にしています。 -/
