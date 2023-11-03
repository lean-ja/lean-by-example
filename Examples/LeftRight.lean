import Mathlib.Tactic.LeftRight

variable (P Q : Prop)

/-! ## left, right -/

example (hP: P) : P ∨ Q := by
  left

  -- ゴールが変わる
  show P

  exact hP

/-! ## left, right を使わない方法 -/

-- 以下に示すように，`Or.inl` は `a` から `a ∨ b` を得る関数です．

/-
Or.inl {a b : Prop} (h : a) : a ∨ b
-/
#check Or.inl

-- `Or.inr` についても同様．

/-
Or.inr {a b : Prop} (h : b) : a ∨ b
-/
#check Or.inr

-- これを使うことで `left` と `right` を使わずに証明できます．

example (hP: P) : P ∨ Q := by
  apply Or.inl
  exact hP
