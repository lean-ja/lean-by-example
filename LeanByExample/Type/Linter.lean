/- # Linter

`Lean.Elab.Command.Linter` は、よくない書き方をされたコードを検出して警告を発してくれるツールです。

```admonish warning title="注意"
このページの内容は <i class="fa fa-play"></i> ボタンから Lean 4 Web で実行することができません。
```
-/

/- ## 使用例

### 選択原理の使用を検出するリンター

選択原理を証明の中で使用すると警告してくれるリンターを自作する例を紹介します。[^dc]
まず以下のように記述したファイルを作成します。

{{#include ./Linter/DetectClassical.md}}

このファイルを読み込むと、次のように使用できます。

{{#include ./Linter/DetectClassicalUse.md}}
-/

/-
### ドキュメントのない定理を検出するリンター

ドキュメントコメントのない `theorem` を見つけて警告を出すリンターを自作する例を紹介します。
まず以下のように記述したファイルを作成します。

{{#include ./Linter/DocBlameThm.md}}

このファイルを読み込むと、次のように使用できます。

{{#include ./Linter/DocBlameThmUse.md}}
-/

/- [^dc]: この例は Lean 公式の Zulip の restricting axioms というトピックにおける、[Damiano Testa さんの投稿](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/restricting.20axioms/near/501743343)を参考にしています。 -/
