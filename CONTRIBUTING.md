# CONTRIBUTING 開発者向け情報

## 依存関係

開発には以下のようなツールを主に利用しています。環境構築済みの DevContainer / GitHub Codespace を用意してありますので、Lean の環境構築をスキップしたい方はそちらを利用してください。

* [mdbook](https://github.com/rust-lang/mdBook) を使用して markdown ファイルから HTML を生成しています。以下のプラグインを使用しています。
  * [mdbook-admonish](https://github.com/tommilligan/mdbook-admonish) を使用してカードを表示させています。
  * [HollowMan6/mdbook-pdf](https://github.com/HollowMan6/mdbook-pdf) を使用して PDF 版を生成しています。PDF 版の生成以外には使用していません。

> [!IMPORTANT]
> 開発に使用する mdbook のバージョンは `0.4.35` に固定してください。`0.4.35` 以外のバージョンではレイアウトが崩れます。

* [mdgen](https://github.com/Seasawher/mdgen) を Lean ファイルから markdown ファイルを生成するために使用しています。
* [mk_exercise](https://github.com/Seasawher/mk-exercise) を使い、Lean の解答ファイルから演習問題ファイルを生成しています。

## 開発の流れ

* このリポジトリは mathlib に依存しているので、このリポジトリを clone した後に `lake exe cache get` を実行してください。
* `Examples/Exercise` 配下のファイルは `mk_exercise` により `Examples/Solution` の内容から自動生成されるので、手動で編集しないでください。
* 本文の markdown ファイルは [mdgen](https://github.com/Seasawher/mdgen) を用いて Lean ファイルから生成します。Lean ファイルを編集した後、`lake run build` コマンドを実行すれば mk_exercise の実行と markdown の生成と `mdbook build` が一括実行されます。

## ルール

* 地の文はですます調とし、コード例の中の文章は常体とします。
* 読点には `、` を、句点には `。` を使用します。ただし例外として、直前の文字が半角文字であるときには `、` の代わりに半角カンマ `,` を使用します。
* 見出しの中でインラインコードを使用すると、PDF版で見栄えが悪くなるので避けてください。
* 見出し語 `foo` に対して、目次の中での記事の名前は `foo: (日本語による一言説明)` とします。可能な限り１行に収まるようにしてください。
* 目次である `src/SUMMARY.md` の内の記事は、カテゴリごとにアルファベット昇順に並べてください。VSCode だと [Tyriar.sort-lines](https://marketplace.visualstudio.com/items?itemName=Tyriar.sort-lines) という拡張機能があって、並び替えを自動で行うことができます。
* Lean コードは、コンパイルが通るようにして `Examples` 配下に配置します。
  * 「エラーになる例」を紹介したいときであっても `try` や `#guard_msgs` や `fail_if_success` などを使ってコンパイルが通るようにしてください。コード例が正しいかチェックする際にその方が楽だからです。
  * Lean ファイルのファイル名は、パスカルケースで命名して下さい。
  * ただしファイル名は、`README` 以外は大文字が連続しないようにします。
