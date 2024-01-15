# README

Lean4 の主要なタクティクを使いたい場面から逆引きできるようにまとめたリストです．

## CONTRIBUTING

誤りの指摘，編集の提案や寄稿を歓迎いたします．この GitHubリポジトリに issue や Pull Request を開いてください．

* 句読点は `,` `.` を使用します．
* タクティク `tactic` に対して，記事の名前は `tactic: (日本語による一言説明)` とします．
* `src/SUMMARY.md` のタクティク記事は，アルファベット昇順に並べてください．VSCode だと `Tyriar.sort-lines` という拡張機能があって，並び替えを自動で行うことができます．
* Lean コードは，コンパイルが通るようにして `Examples` 配下に配置します．「タクティクが失敗する例」を紹介したいときであっても `try` や `#guard_msgs` などを使ってコンパイルが通るようにしてください．コード例が正しいかチェックする際にその方が楽だからです．
* import 文は [import-all](https://github.com/Seasawher/import-all) を用いて自動生成することができるよう設定してあります．
* 本分の markdown ファイルは [mdgen](https://github.com/Seasawher/mdgen) を用いて lean ファイルから生成します．lean ファイルを編集した後，`lake run build` コマンドを実行すれば import 文の更新と markdown の生成と `mdbook build` が一括実行されます．
