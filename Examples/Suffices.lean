import Mathlib.Data.Nat.Order.Lemmas

-- ANCHOR: first
example : 13 ∣ (2 ^ 70 + 3 ^ 70) := by
  -- 余りがゼロであることを示せば十分
  suffices (2 ^ 70 + 3 ^ 70) % 13 = 0 from by
    exact Iff.mpr (Nat.dvd_iff_div_mul_eq (2 ^ 70 + 3 ^ 70) 13) rfl

  rfl
-- ANCHOR_END: first