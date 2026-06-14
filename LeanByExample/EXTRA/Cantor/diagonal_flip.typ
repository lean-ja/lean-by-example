#import "set_map_table.typ": set-map-table
#import "example_map_data.typ": xs, rows

#set page(width: 172mm, height: auto, margin: 8mm)
#set text(size: 11pt)

#let line = rgb("#cbd5e1")
#let header-fill = rgb("#eef4ff")
#let source-column-width = 4.2em
#let arrow-column-width = 1.4em
#let bit-column-width = 2.4em
#let set-column-width = 8.8em

#let flip(value) = if value == 1 { 0 } else { 1 }

#let flipped-bits = (for index in range(rows.len()) {
  (flip(rows.at(index).at(1).at(index)),)
}).flatten()

#let head(body) = table.cell(
  fill: header-fill,
  inset: (x: 7pt, y: 6pt),
)[#strong(body)]

#let spacer = table.cell(colspan: 2, stroke: none)[]

#let bit-cell(value) = table.cell(
  fill: white,
  stroke: line,
  inset: (x: 8pt, y: 6pt),
)[#value]

#let flipped-cells = (for value in flipped-bits {
  (bit-cell(value),)
}).flatten()

#let bit-columns = (for _ in xs {
  (bit-column-width,)
}).flatten()

#let table-columns = (source-column-width, arrow-column-width) + bit-columns + (set-column-width,)

#set-map-table(
  elements: xs,
  rows: rows,
  source-column-width: source-column-width,
  arrow-column-width: arrow-column-width,
  bit-column-width: bit-column-width,
  set-column-width: set-column-width,
  highlight-diagonal: true,
)

#v(0.8em)

#align(center)[
  #text(size: 20pt)[$↓$] \
  #text(size: 10pt)[対角線部分のビットを反転させる]
]

#v(0.6em)

#align(center)[
  #table(
    columns: table-columns,
    align: center + horizon,
    stroke: 0.7pt + line,

    spacer,
    head[$x_1$],
    head[$x_2$],
    head[$x_3$],
    head[$x_4$],
    head[$x_5$],
    head[集合表示],

    spacer,
    ..flipped-cells,
    table.cell(fill: white, inset: (x: 8pt, y: 6pt))[$\{x_2, x_3\}$],
  )
]
