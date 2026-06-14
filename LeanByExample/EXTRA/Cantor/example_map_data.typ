#import "set_map_table.typ": set-map-row

#let xs = ($x_1$, $x_2$, $x_3$, $x_4$, $x_5$)

#let rows = (
  set-map-row($x_1$, (1, 1, 0, 1, 0), $\{x_1, x_2, x_4\}$),
  set-map-row($x_2$, (1, 0, 1, 0, 1), $\{x_1, x_3, x_5\}$),
  set-map-row($x_3$, (0, 0, 0, 0, 0), $\{\}$),
  set-map-row($x_4$, (0, 1, 1, 1, 0), $\{x_2, x_3, x_4\}$),
  set-map-row($x_5$, (1, 0, 0, 1, 1), $\{x_1, x_4, x_5\}$),
)
