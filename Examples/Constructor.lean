variable (P Q : Prop)

/-! ## constructor -/

example (hP: P) (hQ: Q) : P ∧ Q := by
  -- goal が `left` と `right` に分割される
  constructor
  · -- `P` を示す
    exact hP
  · -- `Q` を示す
    exact hQ

/-! ## case を使う書き方 -/

example (hP: P) (hQ: Q) : P ∧ Q := by
  constructor

  case left =>
    exact hP

  case right =>
    exact hQ

/-! ## 同値を示す -/

example (x : Nat) : x = 0 ↔ x + 1 = 1 := by
  constructor
  · -- `x = 0 → x + 1 = 1` を示す
    intro hx
    rw [hx]
  · -- `x + 1 = 1 → x = 0` を示す
    simp_all

/-! ## 逆の，論理積 ∧ を分解する方向 -/

example (h: P ∧ Q) : P := by
  exact h.left

example (h: P ∧ Q) : Q := by
  exact h.right
