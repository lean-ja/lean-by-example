# CONTRIBUTING

## 依存関係

開発には以下のようなツールを主に利用しています。環境構築済みの DevContainer / GitHub Codespace を用意してありますので、Lean の環境構築をスキップしたい方はそちらを利用してください。

* [mdbook](https://github.com/rust-lang/mdBook) を使用して markdown ファイルから HTML を生成しています。以下のプラグインを使用しています。
  * [mdbook-admonish](https://github.com/tommilligan/mdbook-admonish) を使用してカードを表示させています。

> [!IMPORTANT]
> 開発に使用する mdbook のバージョンは `0.4.48` に固定してください。

* [mdgen](https://github.com/Seasawher/mdgen) を Lean ファイルから markdown ファイルを生成するために使用しています。

## 開発の流れ

* このリポジトリは mathlib に依存しているので、このリポジトリを clone した後に `lake exe cache get` を実行してください。
* 本文の markdown ファイルは [mdgen](https://github.com/Seasawher/mdgen) を用いて Lean ファイルから生成します。Lean ファイルを編集した後、`lake run build` コマンドを実行すれば markdown の生成と `mdbook build` が一括実行されます。

## ルール

* 地の文はですます調とし、コード例の中の文章は常体とします。
* 読点には `、` を、句点には `。` を使用します。ただし例外として、直前の文字が半角文字であるときには `、` の代わりに半角カンマ `,` を使用します。
* 見出し語 `foo` に対して、目次の中での記事の名前は `foo: (日本語による一言説明)` とします。可能な限り１行に収まるようにしてください。
* 目次である `booksrc/SUMMARY.md` の内の記事は、カテゴリごとにアルファベット昇順に並べてください。VSCode だと [Tyriar.sort-lines](https://marketplace.visualstudio.com/items?itemName=Tyriar.sort-lines) という拡張機能があって、並び替えを自動で行うことができます。
* Lean コードは、コンパイルが通るようにして `LeanByExample` 配下に配置します。
  * 「エラーになる例」を紹介したいときであっても `try` や `#guard_msgs` や `fail_if_success` などを使ってコンパイルが通るようにしてください。コード例が正しいかチェックする際にその方が楽だからです。
  * Lean ファイルのファイル名は、パスカルケースで命名して下さい。
  * ファイル名は、大文字が連続しないようにします。例外として、`README` はすべて大文字です。また `HDiv` など元々大文字が連続しているものはそのままで構いません。
