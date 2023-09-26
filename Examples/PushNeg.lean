import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.Linarith

variable (P Q : Prop)

-- ANCHOR: first
example (h: P → Q) : ¬ (P ∧ ¬ Q) := by
  -- ドモルガン則を適用して，`¬` を内側に押し込む
  push_neg

  -- `¬` を内側に押し込んだ結果，`¬ P ∨ Q` が得られる
  -- これは `P → Q` と同値
  show P → Q

  exact h
-- ANCHOR_END: first


-- ANCHOR: all_exists
example : ¬ ∃ x : Int , ∀ y : Int, (x + y = 0) := by
  -- ドモルガン則を適用して，`¬` を内側に押し込む
  push_neg

  -- `¬` を内側に押し込んだ結果，ゴールが変わる
  show ∀ x, ∃ y, ¬ (x + y = 0)

  intro x
  exists (- x + 1)
  linarith
-- ANCHOR_END: all_exists