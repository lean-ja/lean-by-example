# Lean4 タクティク逆引きリスト

「普段の数学を Lean でどうやって実現するんだろう」という疑問に答えるために，よく使うタクティクをユースケースから逆引きできるようにまとめたリストです．

なお，タクティクの説明に付記している名前の由来についての説明は公式に説明があったものではなく，あくまで憶測であることをお断りしておきます．

## オプションについて

タクティクによっては，オプションを設定することで挙動を変更することができます．オプションの設定には，`set_option` を使用します．たとえば，`set_option warningAsError true` と書くと，warning(警告) がエラーとして扱われるようになります．

使用できるオプションの一覧は `#help option` で確認することができます．

## リンク集

* [Mathematics in type Theory 日本語訳](https://lean-ja.github.io/math-in-type-theory-ja/) このリストでは「命題は型，証明はその項」という型理論を基礎として数学を実装する際の事実は既知としています．こういった話に全く馴染みがない方は，まずこちらの記事を読まれると良いと思います．

* [mathlib4-all-tactics](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md) 全タクティクの網羅的なリスト．

* [数学系のためのLean勉強会](https://github.com/yuma-mizuno/lean-math-workshop) Lean で数学をどのように実装するのか，実際に実装する過程を追うことで学べる教材です．いくつかコード例を拝借させていただきました．

* [Formalizing Mathematics](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_C/Part_C.html) Lean3 による例ですが，よく使うタクティクを平易な解説とともに紹介しているリストです．コード例や解説を参考にさせていただきました．