#import "set_map_table.typ": set-map-row, set-map-table

#set page(width: 172mm, height: auto, margin: 8mm)
#set text(size: 11pt)

#let xs = ($x_1$, $x_2$, $x_3$, $x_4$, $x_5$)

#let rows = (
  set-map-row($x_1$, (1, 0, 0, 0, 0), $\{x_1\}$),
  set-map-row($x_2$, (1, 0, 0, 0, 0), $\{x_1\}$),
  set-map-row($x_3$, (1, 0, 0, 0, 0), $\{x_1\}$),
  set-map-row($x_4$, (1, 0, 0, 0, 0), $\{x_1\}$),
  set-map-row($x_5$, (1, 0, 0, 0, 0), $\{x_1\}$),
)

#set-map-table(
  elements: xs,
  rows: rows,
)
