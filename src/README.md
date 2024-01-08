# Lean4 タクティク逆引きリスト

「普段の数学を Lean でどうやって実現するんだろう」という疑問に答えるために，よく使うタクティクをユースケースから逆引きできるようにまとめたリストです．より便利にするため，タクティクだけでなく基本的なコマンドも紹介しています．

なおこのタクティクリストは全タクティクのリストではありません．全タクティクのリストを見るには，[#help](./help.md)コマンドを使用してください．

> この文書は lean-ja が管理しています．誤りのご指摘，ご提案などは [GitHub リポジトリ](https://github.com/lean-ja/tactic-cheatsheet)からお願いします．
>
> lean-ja の Discord サーバが[こちら](https://discord.gg/p32ZfnVawh)にあります．質問や相談などはこちらにどうぞ．

## 本書の特色 😎

* 本書のすべての Lean コードブロックはバージョン `{{#include ../lean-toolchain}}` で実際にエラーなく動くことを CI で確認しています．動かないコード例を見つけられた際はお手数ですが issue でご報告をお願いします．

* 本書のすべての Lean コードブロックは，マウスを重ねると Lean Playground へジャンプするボタン <a class="fa fa-external-link"></a> が現れるようになっています. ぜひ実際にコードを実行してみてください．

* `import` 文がないコードブロックの中には，そのままでは実行できないものがあります．そうした場合は画面右上の実行ボタン <i class="fa fa-play"></i> をクリックしてください．

## リンク集 🌐

* [数学系のためのLean勉強会](https://github.com/yuma-mizuno/lean-math-workshop) Lean で数学をどのように実装するのか，実際に実装する過程を追うことで学べる教材です．いくつかコード例を拝借させていただきました．

* [Theorem Proving in Lean 4 日本語訳](https://aconite-ac.github.io/theorem_proving_in_lean4_ja/) Lean で数学の証明を行う方法を解説した公式チュートリアルの，有志による日本語訳です．

* [Lean phrasebook](https://docs.google.com/spreadsheets/d/1Gsn5al4hlpNc_xKoXdU6XGmMyLiX4q-LFesFVsMlANo/edit#gid=0) 英語ですが，数学でのよくある推論ステップが，Lean にどのように翻訳されるかがよくまとめられたリストです．