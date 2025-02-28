/- # Lean by Example

プログラミング言語であるとともに定理証明支援系でもある Lean 言語と、その主要なライブラリの使い方を豊富なコード例とともに解説した資料です。

```admonish info title=""
本書は lean-ja の管理者である[北窓](https://github.com/Seasawher)が執筆・開発しています。誤りのご指摘、ご提案などは [GitHub リポジトリ](https://github.com/lean-ja/lean-by-example)からお願いします。

lean-ja の Discord サーバが[こちら](https://discord.gg/p32ZfnVawh)にあります。質問や相談などはこちらにどうぞ。
```

本書が気に入ったら、ぜひ GitHub からスター🌟をつけてください。

## 本書の特色 😎

### 1. 内容が正確
Lean は開発が活発に続いているソフトウェアであり、毎月のように新しいリリースが行われています。その際破壊的な変更が行われることは少なくありません。変更によって古くなってしまった記述を自動的に見つける方法がなければ、内容の信頼性が損なわれます。

本書では、この問題に対して次のように対処しています。

* 記述内容を可能な限りコードとして表現することにより、「ビルドが通れば記述内容は正しい」という状態を維持する。
* 内容を更新するごとにビルドが自動的に走るようにする。

これにより本書のほぼすべての記述はバージョン `{{#include ../lean-toolchain}}` で実際に間違いがないということを確認済みです。

間違った記述を見つけられた際はお手数ですが issue でご報告をお願いします。

### 2. 情報が新しい
本書は、Lean とそのライブラリのバージョンを自動で更新するワークフロー [lean-update](https://github.com/Seasawher/lean-update) を利用して、定期的にバージョンを最新のものに更新しています。Lean の最新情報をすべて掲載することはかないませんが、最新の情報を提供できるよう努めています。

### 3. コードをすぐに試せる
本書のすべての Lean コードブロックは、マウスを重ねると Lean Playground へジャンプするボタン <i class="fa fa-external-link"></i> が現れるようになっています。

またコードブロックの中には、`import` 文が足りないなどの理由でそのままでは実行できないものがありますが、そうした場合は画面右上の実行ボタン <i class="fa fa-play"></i> をクリックしていただければ、ファイル全体を実行することができます。

このようなことが可能なのは、[mdgen](https://github.com/Seasawher/mdgen) を使って、Lean コードから markdown ファイルを生成することにより本書が制作されているからです。

### 4. わかりやすい

「わかりやすさ」にも種類があります。世の中には「難しい部分を隠蔽する」ことをもって「わかりやすい」としている書籍も存在しますが、本書はその立場をとりません。

では何をもってわかりやすいと考えているかというと、まず本書では「ほぼすべての記述がコード例によって検証されている」ので、言い換えれば「どの記述にもコード例が付随している」ということになります。これにより、「そもそも何を言っているのかわからない記述」が本書にはほとんど存在しないはずです。

また、「ほぼすべての記述がコード例によって検証されている」ということは、「コード例で検証できないことには言及できない」ことになります。これにより、本書の記述は「それが何であるのか」の詳しい説明が少なく、「それを使って何ができるのか」の説明が多くなっています。これにより、結果として説明がより具体的かつ実践的になり、特に初学者にとってより理解しやすくなるという効果が生じているはずです。

## スポンサー

このプロジェクトは [Proxima Technology](https://proxima-ai-tech.com/) 様よりご支援を頂いています。

![logo of Proxima Technology](./image/proxima.svg)

Proxima Technology（プロキシマテクノロジー）は数学の社会実装を目指し、その⼀環としてモデル予測制御の民主化を掲げているAIスタートアップ企業です。数理科学の力で社会を変えることを企業の使命としています。

-/
