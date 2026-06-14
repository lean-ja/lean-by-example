#let set-map-row(source, bits, set-label) = (source, bits, set-label)

#let set-map-table(
  elements: (),
  rows: (),
  x-label: $X$,
  arrow: $↦$,
  bit-header: [$f(x)$ のビット表示],
  set-header: [集合表示],
  source-column-width: 4.2em,
  arrow-column-width: 1.4em,
  bit-column-width: 2.4em,
  set-column-width: 6.4em,
  line-color: rgb("#cbd5e1"),
  header-fill: rgb("#eef4ff"),
  subheader-fill: rgb("#f8fafc"),
  one-fill: rgb("#dbeafe"),
) = {
  let head(body) = table.cell(
    fill: header-fill,
    inset: (x: 7pt, y: 6pt),
  )[#strong(body)]

  let subhead(body) = table.cell(
    fill: subheader-fill,
    inset: (x: 7pt, y: 5pt),
  )[#body]

  let x-cell(body) = table.cell(
    fill: subheader-fill,
    inset: (x: 8pt, y: 6pt),
  )[#body]

  let bit(value) = table.cell(
    fill: if value == 1 { one-fill } else { white },
    stroke: line-color,
    inset: (x: 8pt, y: 6pt),
  )[#value]

  let bit-columns = (for _ in elements {
    (bit-column-width,)
  }).flatten()

  let columns = (source-column-width, arrow-column-width) + bit-columns + (set-column-width,)

  let element-cells = (for element in elements {
    (subhead(element),)
  }).flatten()

  let row-cells = (for row in rows {
    let source = row.at(0)
    let bits = row.at(1)
    let set-label = row.at(2)
    let bit-cells = (for value in bits {
      (bit(value),)
    }).flatten()

    (x-cell(source), table.cell(stroke: none)[#arrow]) + bit-cells + (x-cell(set-label),)
  }).flatten()

  align(center)[
    #table(
      columns: columns,
      align: center + horizon,
      stroke: 0.7pt + line-color,

      head(x-label),
      table.cell(stroke: none)[],
      table.cell(colspan: elements.len(), fill: header-fill, inset: (x: 7pt, y: 6pt))[
        #strong(bit-header)
      ],
      head(set-header),

      subhead[],
      table.cell(stroke: none)[],
      ..element-cells,
      subhead[],

      ..row-cells,
    )
  ]
}
