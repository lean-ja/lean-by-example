#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set page(width: 110mm, height: auto, margin: 8mm)
#set text(size: 15pt)

#let ink = rgb("#1f2937")
#let muted = rgb("#4b5563")
#let code-ink = rgb("#0f5f77")

#align(center)[
  #stack(
    dir: ttb,
    spacing: 8pt,
    diagram(spacing: 3.35em, edge-stroke: 0.055em + ink, {
      node((-2, -1), text(fill: ink)[$alpha$])
      node((0, -1), text(fill: ink)[$beta$])
      node((-2, 1), text(fill: ink)[$F alpha$])
      node((0, 1), text(fill: ink)[$F beta$])
      edge((-2, -1), (0, -1), text(fill: ink)[$f$], label-side: left, "->")
      edge((-2, 1), (0, 1), text(fill: ink)[$F_* f$], label-side: right, "->", stroke: ink)
      edge((-1, -0.8), (-1, 0.8), text(fill: ink)[$F$], label-side: center, "-->", stroke: ink)
    }),
    block(width: 86mm)[
      #align(left, text(size: 8pt, fill: muted)[
        この図では、#text(fill: code-ink)[`Functor.map`] に使用されている関手を明示するために\
        $F_*$ という書き方を採用しています。
      ])
    ],
  )
]
