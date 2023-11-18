# Lean4 タクティク逆引きリスト

「普段の数学を Lean でどうやって実現するんだろう」という疑問に答えるために，よく使うタクティクをユースケースから逆引きできるようにまとめたリストです．タクティクだけでなく，基本的なコマンドも紹介しています．

ほぼすべてのコード例はバージョン `{{#include ../lean-toolchain}}` で実際に動くことを確認済みです．

この本のすべての Lean コードブロックは，マウスを重ねると Lean Playground へジャンプするボタン <a class="fa fa-external-link"></a> が現れるようになっています. ぜひ実際にコードを実行してみてください．

> この文書は lean-ja が管理しています．
>
> 誤りのご指摘，ご提案などは [GitHub リポジトリ](https://github.com/lean-ja/tactic-cheetsheet)からお願いします．
> また lean-ja の Discord サーバが[こちら](https://discord.gg/p32ZfnVawh)にあります．

## 全タクティクのリストを見る方法

このリストは全タクティクのリストではありません．全タクティクのリストが必要な場合，以下のコードで確認することができます．

```lean
import Mathlib.Tactic

#help tactic
```

## オプションについて

タクティクによっては，オプションを設定することで挙動を変更することができます．オプションの設定には，`set_option` を使用します．たとえば，`set_option warningAsError true` と書くと，warning(警告) がエラーとして扱われるようになります．

使用できるオプションの一覧は次のコマンドで確認できます．

```lean
import Mathlib.Tactic

#help option
```

## リンク集

* [数学系のためのLean勉強会](https://github.com/yuma-mizuno/lean-math-workshop) Lean で数学をどのように実装するのか，実際に実装する過程を追うことで学べる教材です．いくつかコード例を拝借させていただきました．

* [Lean phrasebook](https://docs.google.com/spreadsheets/d/1Gsn5al4hlpNc_xKoXdU6XGmMyLiX4q-LFesFVsMlANo/edit#gid=0) 英語ですが，数学でのよくある推論ステップが，Lean にどのように翻訳されるかがよくまとめられたリストです．