/- # by_contra

`by_contra` は、背理法を使いたいときに役立つタクティクです。

ゴールが `⊢ P` であるときに `by_contra h` を実行すると、`h : ¬ P` がローカルコンテキストに追加されて、同時にゴールが `⊢ False` になります。
-/
import Mathlib.Tactic.ByContra

variable (P Q : Prop)

example (h: ¬Q → ¬P) : P → Q := by
  -- `P` であると仮定する
  intro hP

  -- `¬Q` であると仮定して矛盾を導きたい
  by_contra hnQ
  show False

  -- `¬ Q → ¬ P` と `¬Q` から `¬P` が導かれる
  have := h hnQ

  -- これは仮定に矛盾
  contradiction
