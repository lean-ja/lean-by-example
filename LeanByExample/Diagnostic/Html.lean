/- # \#html

`#html` コマンドは、その名の通り html をインフォビューに表示させるコマンドです。[ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4) というライブラリで定義されています。

[JSX](https://ja.react.dev/learn/writing-markup-with-jsx) によく似た構文を使うことができます。
-/
import ProofWidgets

-- JSX ライクな構文が使えるようにする
open scoped ProofWidgets.Jsx

#html <p>"ここに HTML を書きます"</p>

-- いろんなHTMLタグを書くことができる
#html
  <div>
    <h3>"見出し"</h3>
    <p>
      <b>"強調されたテキスト"</b>
      <i>"斜体のテキスト"</i>
    </p>
    <a href="https://lean-lang.org/">"リンク"</a>
  </div>

-- 画像も表示できる
#html
  <img src={"https://upload.wikimedia.org/wikipedia/commons/6/6a/Julia-set_N_z3-1.png"}
    alt="julia set"/>

/- ## コンポーネント紹介

HTMLタグを使用できるだけでなく、様々なコンポーネントが定義されています。-/

/- ### MarkdownDisplay

`<MarkdownDisplay />` コンポーネントを使用すると、Markdown や TeX を表示させることができます。

{{#include ./Html/MarkdownDisplay.md}}
-/

/- ### GraphDisplay

`<GraphDisplay />` コンポーネントを使用すると、有向グラフを表示させることができます。

{{#include ./Html/GraphDisplay.md}}
-/

/- ### LineChart

ProofWidgets4 には [Recharts ライブラリ](https://recharts.org/en-US) に対するサポートがあり、`<LineChart />` コンポーネントを使用すると、関数のグラフを表示させることができます。

{{#include ./Html/LineChart.md}}
-/

/- ## 使用例

`#html` コマンドを使うと SVG 画像を infoview 内で直接表示させることができるという点、さらに ProofWidgets が SVG 画像の作成をある程度サポートしているという点を利用すると、「二分木を画像として infoview に表示させる」ということが可能です。[^bintree]

{{#include ./Html/BinTree.md}}
-/

/-
[^bintree]: この例を作成するにあたり、lean-ja Discord サーバーで todaymint さんにご助力をいただきました。
-/
