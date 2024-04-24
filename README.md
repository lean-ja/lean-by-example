# README

![workflow](https://github.com/lean-ja/tactic-cheatsheet/actions/workflows/ci.yml/badge.svg) ![workflow](https://github.com/lean-ja/tactic-cheatsheet/actions/workflows/deploy.yml/badge.svg)

Lean4 の主要なタクティクを使いたい場面から逆引きできるようにまとめたリストです．

## CONTRIBUTING

誤りの指摘，編集の提案や寄稿を歓迎いたします．この GitHubリポジトリに issue や Pull Request を開いてください．

* 句読点は `,` `.` を使用します．
* タクティク `tactic` に対して，記事の名前は `tactic: (日本語による一言説明)` とします．
* `src/SUMMARY.md` のタクティク記事は，アルファベット昇順に並べてください．VSCode だと `Tyriar.sort-lines` という拡張機能があって，並び替えを自動で行うことができます．
* Lean コードは，コンパイルが通るようにして `Examples` 配下に配置します．「タクティクが失敗する例」を紹介したいときであっても `try` や `#guard_msgs` などを使ってコンパイルが通るようにしてください．コード例が正しいかチェックする際にその方が楽だからです．
* 本文の markdown ファイルは [mdgen](https://github.com/Seasawher/mdgen) を用いて lean ファイルから生成します．lean ファイルを編集した後，`lake run build` コマンドを実行すれば markdown の生成と `mdbook build` が一括実行されます．

## スポンサー

このプロジェクトは [Proxima Technology](https://proxima-ai-tech.com/) 様よりご支援を頂いています.

![logo of Proxima Technology](./src/image/proxima.png)

Proxima Technology（プロキシマテクノロジー）は数学の社会実装を目指し, その⼀環としてモデル予測制御の民主化を掲げているAIスタートアップ企業です．数理科学の力で社会を変えることを企業の使命としています．
