/*
全射版カントールの定理の証明の中では、全射 `f : X → Set X` が存在すると仮定したときに、そこから `{x | x ∉ f x}` という集合を作ってくるところが核心でした。このテクニックは **対角線論法(diagonal argument)** と呼ばれます。

なんで「対角線」なのか疑問に思われたでしょうか？これは、図解してみるとわかります。

たとえば、`X = {x₁, x₂, x₃, x₄, x₅}` という有限集合を考えましょう。ここでどのような関数 `f : X → Set X` が与えられたとしても、`f` の像に入っていない部分集合 `T : Set X` を構成する具体的な手続きがあるかどうか考えてみましょう。

まず、`X` の部分集合は各 `xᵢ` を含んでいるか含んでいないかの長さ5のビット列で表すことができます。それぞれ `1` と `0` で表すことにすれば、`X` の部分集合は `[0, 1, 1, 1, 0]` のように表すことができることになります。そう考えると、各 `f : X → Set X` は２次元の表で表すことができます。

たとえば、常に `{x₁}` という１点集合を返す関数 `f` は次の表と対応します。
*/

#set page(width: 172mm, height: auto, margin: 8mm)
#set text(size: 11pt)

#let line = rgb("#cbd5e1")
#let header-fill = rgb("#eef4ff")
#let subheader-fill = rgb("#f8fafc")
#let one-fill = rgb("#dbeafe")

#let head(body) = table.cell(
  fill: header-fill,
  inset: (x: 7pt, y: 6pt),
)[#strong(body)]

#let subhead(body) = table.cell(
  fill: subheader-fill,
  inset: (x: 7pt, y: 5pt),
)[#body]

#let x-cell(body) = table.cell(
  fill: subheader-fill,
  inset: (x: 8pt, y: 6pt),
)[#body]

#let bit(value) = table.cell(
  fill: if value == 1 { one-fill } else { white },
  stroke: line,
  inset: (x: 8pt, y: 6pt),
)[#value]

#align(center)[
  #table(
    columns: (4.2em, 1.4em, 2.4em, 2.4em, 2.4em, 2.4em, 2.4em, 6.4em),
    align: center + horizon,
    stroke: 0.7pt + line,

    head[$X$],
    table.cell(stroke: none)[],
    table.cell(colspan: 5, fill: header-fill, inset: (x: 7pt, y: 6pt))[
      #strong[$f(x)$ のビット表示]
    ],
    head[集合表示],

    subhead[],
    table.cell(stroke: none)[],
    subhead[$x_1$],
    subhead[$x_2$],
    subhead[$x_3$],
    subhead[$x_4$],
    subhead[$x_5$],
    subhead[],

    x-cell[$x_1$],
    table.cell(stroke: none)[$↦$],
    bit(1),
    bit(0),
    bit(0),
    bit(0),
    bit(0),
    x-cell[$\{x_1\}$],

    x-cell[$x_2$],
    table.cell(stroke: none)[$↦$],
    bit(1),
    bit(0),
    bit(0),
    bit(0),
    bit(0),
    x-cell[$\{x_1\}$],

    x-cell[$x_3$],
    table.cell(stroke: none)[$↦$],
    bit(1),
    bit(0),
    bit(0),
    bit(0),
    bit(0),
    x-cell[$\{x_1\}$],

    x-cell[$x_4$],
    table.cell(stroke: none)[$↦$],
    bit(1),
    bit(0),
    bit(0),
    bit(0),
    bit(0),
    x-cell[$\{x_1\}$],

    x-cell[$x_5$],
    table.cell(stroke: none)[$↦$],
    bit(1),
    bit(0),
    bit(0),
    bit(0),
    bit(0),
    x-cell[$\{x_1\}$],
  )
]
