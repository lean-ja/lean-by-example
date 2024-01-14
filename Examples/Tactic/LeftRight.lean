/- # left, right

ゴールが `⊢ P ∨ Q` であるとき，`left` はゴールを `⊢ P` に，`right` はゴールを `⊢ Q` に変えます． -/
import Std.Tactic.LeftRight

variable (P Q : Prop)

example (hP: P) : P ∨ Q := by
  left

  -- ゴールが変わる
  show P

  exact hP

/-! ## left, right を使わない方法

以下に示すように，`Or.inl` は `a` から `a ∨ b` を得る関数です．また `Or.inr` は `b` から `a ∨ b` を得る関数です．これを使うことで `left` や `right` を使わずに証明できます．
-/

-- Or.inl {a b : Prop} (h : a) : a ∨ b
#check Or.inl

-- Or.inr {a b : Prop} (h : b) : a ∨ b
#check Or.inr

example (hP: P) : P ∨ Q := by
  apply Or.inl
  exact hP
