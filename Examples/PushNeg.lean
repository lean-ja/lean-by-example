import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Linarith

variable (P Q : Prop)

/-! ## push_neg -/

example (h: P → Q) : ¬ (P ∧ ¬ Q) := by
  -- ドモルガン則を適用して，`¬` を内側に押し込む
  push_neg

  -- デフォルトの設定だと `P → Q` に変形される
  show P → Q

  exact h

/-!
  ## use_distrib

  option で `push_neg.use_distrib` を `true` にすると，
  `¬ (p ∧ q)` を `¬ p ∨ ¬ q` に変形する．
-/

set_option push_neg.use_distrib true

example (h: P → Q) : ¬ (P ∧ ¬ Q) := by
  -- ドモルガン則を適用して，`¬` を内側に押し込む
  push_neg

  -- goal が論理和の形になる
  show ¬ P ∨ Q

  -- 場合分けで示す
  by_cases hP : P
  · right
    exact h hP
  · left
    assumption

/-! ## 量化子に対して使った場合 -/

example : ¬ ∃ (x : ℤ), ∀ (y : ℤ), (x + y = 0) := by
  -- ドモルガン則を適用して，`¬` を内側に押し込む
  push_neg

  -- `¬` を内側に押し込んだ結果，ゴールが変わる
  show ∀ x, ∃ y, ¬ (x + y = 0)

  intro x
  exists (- x + 1)
  linarith
