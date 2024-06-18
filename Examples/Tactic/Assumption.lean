/-! # assumption

`assumption` は，現在のゴール `⊢ P` がローカルコンテキストにあるとき，ゴールを閉じます．-/

variable (P Q : Prop)

example (hP: P) (_: Q) : P := by
  assumption

/-! ## exact との関連

`assumption` による証明は，どの仮定を使うか明示すれば [`exact`](./Exact.md) で書き直すことができます．-/

example (hP: P) (_: Q) : P := by
  exact hP
