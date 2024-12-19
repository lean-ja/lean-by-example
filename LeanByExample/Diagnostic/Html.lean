/- # \#html

`#html` コマンドは、その名の通り html をインフォビューに表示させるコマンドです。[ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4) というライブラリで定義されています。

[JSX](https://ja.react.dev/learn/writing-markup-with-jsx) によく似た構文を使うことができます。
-/
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Recharts
import ProofWidgets.Component.GraphDisplay

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

/- HTMLタグを使用できるだけでなく、様々なコンポーネントが定義されています。-/

/- ## MarkdownDisplay

`<MarkdownDisplay />` コンポーネントを使用すると、Markdown や TeX を表示させることができます。

```admonish warning title="注意"
`MarkdownDisplay` の例は Lean 4 Playground では動作しないようです。VSCode 上で試してみてください。
```
-/
section --#

open ProofWidgets

-- Markdown と TeX を表示する
#html <MarkdownDisplay contents={"
  ## Riemann zeta function

  The Riemann zeta function is defined as
  $$
  \\zeta(s) = \\sum_{n=1}^∞ \\frac{1}{n^s}
  $$

  for $\\mathrm{Re} (s) > 0$.
"}/>

end --#
/- ## GraphDisplay

`<GraphDisplay />` コンポーネントを使用すると、有向グラフを表示させることができます。
-/
section --#

open ProofWidgets Jsx GraphDisplay

/-- `Edge` を作る -/
def mkEdge (st : String × String) : Edge := {source := st.1, target := st.2}

/-- 文字列として与えられたラベルから `Vertex` を作る -/
def mkVertex (id : String) : Vertex := {id := id}

-- 有向グラフを表示する
#html
  <GraphDisplay
    vertices={#["a", "b", "c", "d", "e"].map mkVertex}
    edges={#[("a","b"), ("b","c"), ("c","d"), ("d","e"), ("e", "a")].map mkEdge}
  />

end --#
/- ## LineChart

ProofWidgets4 には [Recharts ライブラリ](https://recharts.org/en-US) に対するサポートがあり、`<LineChart />` コンポーネントを使用すると、関数のグラフを表示させることができます。
-/
section --#

open Lean ProofWidgets Recharts

open scoped ProofWidgets.Jsx in

/-- 与えられた関数 `fn` の `[0, 1]` 区間上での値のグラフ -/
def Plot (fn : Float → Float) (steps := 100) : Html :=
  -- `[0, 1)` 区間を `steps` 個に分割する
  let grids := Array.range steps
    |>.map (fun x => x.toFloat / steps.toFloat)

  -- データを JSON に変換
  let y := grids.map fn
  let jsonData : Array Json := grids.zip y
    |>.map (fun (x,y) => json% {x: $(toJson x) , y: $(toJson y)});

  <LineChart width={400} height={400} data={jsonData}>
    <XAxis dataKey?="x" />
    <YAxis dataKey?="y" />
    <Line type={.monotone} dataKey="y" stroke="#8884d8" dot?={Bool.false} />
  </LineChart>

#html Plot (fun x => (x - 0.3) ^ 2 + 0.1)
#html Plot (fun x => 0.2 + 0.5 * Float.sin (7 * x))

end --#
