#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set page(width: 100mm, height: auto, margin: 8mm)
#set text(size: 12pt)

#align(center, diagram({
	node((-2, -1), [$alpha$])
	node((0, -1), [$beta$])
	node((-2, 1), [$F alpha$])
	node((0, 1), [$F beta$])
	edge((-2, -1), (0, -1), [$f$], label-side: left, "->")
	edge((-2, 1), (0, 1), [$F_* f$], label-side: right, "->")
	edge((-1, -0.8), (-1, 0.8), [$F$], label-side: center, "-->")
}))
