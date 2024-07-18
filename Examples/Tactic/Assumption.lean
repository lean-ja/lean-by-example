/-! # assumption

`assumption` は、現在のゴール `⊢ P` がローカルコンテキストにあるとき、ゴールを閉じます。-/

variable (P Q : Prop)

example (hP: P) (_: Q) : P := by
  assumption

/- `assumption` による証明は、どの仮定を使うか明示すれば [`exact`](./Exact.md) で書き直すことができます。`assumption` を使用することにより、仮定の名前の変更に対してロバストになるほか、意図がわかりやすくなるというメリットがあります。-/

example (hP: P) (_: Q) : P := by
  exact hP
