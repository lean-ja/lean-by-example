// リポジトリのルートで実行する。
// typst compile LeanByExample/EXTRA/PowerFixPoint/fixed_point.typ LeanByExample/EXTRA/PowerFixPoint/fixed_point.svg
// Typst 0.14.2。外部パッケージは使用しない。

#set page(width: 156mm, height: 139mm, margin: 0pt, fill: white)
#set text(font: "New Computer Modern", size: 19pt)

#let ink = rgb("#171b22")
#let accent = rgb("#07869c")
#let highlight = rgb("#83f2ef")
#let graph-stroke = (paint: ink, thickness: 2pt, cap: "round", join: "round")
#let accent-stroke = (paint: accent, thickness: 1.8pt, cap: "round", join: "round")

// 座標は左上を原点とし、単位を mm にそろえる。
#let point(x, y) = (x * 1mm, y * 1mm)
#let origin = (28, 91)
#let axis-end = 106
#let axis-top = 13
#let u = 83
#let fixed-y = origin.at(1) - (u - origin.at(0))

#let segment(start, end, stroke: graph-stroke) = place(
  top + left,
  curve(stroke: stroke, curve.move(point(..start)), curve.line(point(..end))),
)

#let dot(x, y, radius: 1.65mm) = place(
  top + left,
  dx: x * 1mm - radius,
  dy: y * 1mm - radius,
  circle(radius: radius, fill: ink, stroke: none),
)

// ラベルを指定した座標の中心に配置する。
#let label(x, y, body, size: 19pt, fill: ink) = context {
  let body = text(size: size, fill: fill, body)
  let bounds = measure(body)
  place(
    top + left,
    dx: x * 1mm - bounds.width / 2,
    dy: y * 1mm - bounds.height / 2,
    body,
  )
}

// 𝒟 に対応する区間。軸の背面に水色の線を重ねる。
#segment(
  (origin.at(0), origin.at(1) + 1),
  (u, origin.at(1) + 1),
  stroke: (paint: highlight, thickness: 7pt, cap: "round"),
)

// 座標軸と矢尻。
#segment(origin, (axis-end, origin.at(1)))
#segment(origin, (origin.at(0), axis-top))
#place(top + left, curve(
  stroke: graph-stroke,
  curve.move(point(axis-end - 2.8, origin.at(1) - 2.4)),
  curve.line(point(axis-end, origin.at(1))),
  curve.line(point(axis-end - 2.8, origin.at(1) + 2.4)),
  curve.move(point(origin.at(0) - 2.4, axis-top + 2.8)),
  curve.line(point(origin.at(0), axis-top)),
  curve.line(point(origin.at(0) + 2.4, axis-top + 2.8)),
))

// 対角線 y = x。
#segment(origin, (axis-end, axis-top))

// 単調写像 y = Φ(x)。交点の付近では水平になり、その後再び増加する。
#place(top + left, curve(
  stroke: graph-stroke,
  curve.move(point(origin.at(0), 54)),
  curve.cubic(point(44, 40), point(59, fixed-y), point(70, fixed-y)),
  curve.cubic(point(75, fixed-y), point(79, fixed-y), point(u, fixed-y)),
  curve.cubic(point(94, fixed-y), point(99, 33), point(axis-end, 26)),
))

// 交点から U へ下ろした点線。
#for index in range(1, 20) {
  let y = fixed-y + (origin.at(1) - fixed-y) * index / 20
  dot(u, y, radius: 0.55mm)
}
#dot(u, fixed-y)
#dot(u, origin.at(1))

#label(18, axis-top, $X$)
#label(axis-end + 1, 100, $X$)
#label(19, origin.at(1), $emptyset$)
#label(origin.at(0), 100, $emptyset$)
#label(u, 100, $U$)
#label(106, 5.5, $y = x$)
#label(126, 23, $y = Phi(x)$)

// 下の定義から、強調した区間を指す矢印。
#let pointer-x = 53
#segment((pointer-x, 118), (pointer-x, 97), stroke: accent-stroke)
#place(top + left, curve(
  stroke: accent-stroke,
  curve.move(point(pointer-x - 2.2, 99.4)),
  curve.line(point(pointer-x, 97)),
  curve.line(point(pointer-x + 2.2, 99.4)),
))
#label(78, 130, $cal(D) = { S : "Set" X | S subset.eq Phi(S) }$, size: 20pt, fill: accent)
