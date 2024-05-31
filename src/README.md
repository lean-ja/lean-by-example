# Lean4 タクティク逆引きリスト

「普段の数学を Lean でどうやって実現するんだろう」という疑問に答えるために，Lean や Mathlib のよく使うタクティクをユースケースから逆引きできるようにまとめたリストです．より便利にするため，タクティクだけでなく基本的なコマンドも紹介しています．

なおこのタクティクリストは全タクティクのリストではありません．全タクティクのリストが必要であれば [mathlib4 tactics](https://seasawher.github.io/mathlib4-tactics) を参照してください．

> この文書は lean-ja が管理しています．誤りのご指摘，ご提案などは [GitHub リポジトリ](https://github.com/lean-ja/tactic-cheatsheet)からお願いします．
>
> lean-ja の Discord サーバが[こちら](https://discord.gg/p32ZfnVawh)にあります．質問や相談などはこちらにどうぞ．

本書が気に入ったら，ぜひ GitHub からスター🌟をつけてください.

## 本書の特色 😎

* 本書のすべての Lean コードブロックはバージョン `{{#include ../lean-toolchain}}` で実際にエラーなく動くことを CI で確認しています．動かないコード例を見つけられた際はお手数ですが issue でご報告をお願いします．

* 本書のすべての Lean コードブロックは，マウスを重ねると Lean Playground へジャンプするボタン <a class="fa fa-external-link"></a> が現れるようになっています. ぜひ実際にコードを実行してみてください．

* コードブロックの中には，`import` 文が足りないなどの理由でそのままでは実行できないものがあります．そうした場合は画面右上の実行ボタン <i class="fa fa-play"></i> をクリックしてください．

## スポンサー

このプロジェクトは [Proxima Technology](https://proxima-ai-tech.com/) 様よりご支援を頂いています.

![logo of Proxima Technology](./image/proxima.svg)

Proxima Technology（プロキシマテクノロジー）は数学の社会実装を目指し, その⼀環としてモデル予測制御の民主化を掲げているAIスタートアップ企業です．数理科学の力で社会を変えることを企業の使命としています．
