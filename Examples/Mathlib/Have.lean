import Mathlib.Tactic.Ring

-- ANCHOR: exists

-- `x`が偶数のとき`3 * x`も偶数
example (x : ℕ) (hx : ∃ y, x = 2 * y) : ∃ z, 3 * x = 2 * z := by
  -- `hx` で存在が主張されている `y` と，
  -- `x = 2 * y` という命題を得る
  have ⟨y, hy⟩ := hx
  exists 3 * y
  rw [hy]
  ring
-- ANCHOR_END: exists