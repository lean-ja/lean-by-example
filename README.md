# README

[![repo logo](./src/image/project_image.png)]()

[![workflow](https://github.com/lean-ja/lean-by-example/actions/workflows/ci.yml/badge.svg)](https://github.com/lean-ja/lean-by-example/blob/main/.github/workflows/ci.yml) [![workflow](https://github.com/lean-ja/lean-by-example/actions/workflows/deploy.yml/badge.svg)](https://github.com/lean-ja/lean-by-example/blob/main/.github/workflows/deploy.yml) [![workflow](https://github.com/lean-ja/lean-by-example/actions/workflows/update.yml/badge.svg)](https://github.com/lean-ja/lean-by-example/blob/main/.github/workflows/update.yml) [![workflow](https://github.com/lean-ja/lean-by-example/actions/workflows/devcontainer.yml/badge.svg)](https://github.com/lean-ja/lean-by-example/blob/main/.github/workflows/devcontainer.yml) [![discord](https://dcbadge.limes.pink/api/server/p32ZfnVawh?style=flat)](https://discord.gg/p32ZfnVawh)

プログラミング言語であるとともに定理証明支援系でもある Lean 言語と、その主要なライブラリの使い方を豊富なコード例とともに解説した資料です。

> [!WARNING]
> 本書は現在開発中であり、各ページのURLが予告なく変更され、リダイレクトも設定されないということがあり得ます。リンク切れを避けるには、個別ページではなくトップページにリンクを張るようにしてください。

## CONTRIBUTING

誤りの指摘、編集の提案や寄稿を歓迎いたします。この GitHubリポジトリに issue や Pull Request を開いてください。

環境構築済みの DevContainer / GitHub Codespace を用意してありますので、Lean の環境構築をスキップしたい方はそちらを利用してください。

* 読点には `、` を、句点には `。` を使用します。
* 地の文はですます調とし、コード例の中の文章は常体とします。
* 見出し語 `foo` に対して、目次の中での記事の名前は `foo: (日本語による一言説明)` とします。可能な限り１行に収まるようにしてください。
* 本書では [mdbook](https://github.com/rust-lang/mdBook) を使用して markdown ファイルから HTML を生成しています。
* 目次である `src/SUMMARY.md` の内の記事は、カテゴリごとにアルファベット昇順に並べてください。VSCode だと [Tyriar.sort-lines](https://marketplace.visualstudio.com/items?itemName=Tyriar.sort-lines) という拡張機能があって、並び替えを自動で行うことができます。
* 本文の markdown ファイルは [mdgen](https://github.com/Seasawher/mdgen) を用いて Lean ファイルから生成します。Lean ファイルを編集した後、`lake run build` コマンドを実行すれば markdown の生成と `mdbook build` が一括実行されます。
* Lean コードは、コンパイルが通るようにして `Examples` 配下に配置します。「エラーになる例」を紹介したいときであっても `try` や `#guard_msgs` や `fail_if_success` などを使ってコンパイルが通るようにしてください。コード例が正しいかチェックする際にその方が楽だからです。

## Do you want to translate this book?

Thank you for your interest in translating this book! 😄 But please note that we are currently **not accepting translations** of this book because this book is still under development! No content is stable yet.

## スポンサー

このプロジェクトは [Proxima Technology](https://proxima-ai-tech.com/) 様よりご支援を頂いています。

![logo of Proxima Technology](./src/image/proxima.svg)

Proxima Technology（プロキシマテクノロジー）は数学の社会実装を目指し、その⼀環としてモデル予測制御の民主化を掲げているAIスタートアップ企業です。数理科学の力で社会を変えることを企業の使命としています。
