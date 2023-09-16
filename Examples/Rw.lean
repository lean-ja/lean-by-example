example (a b c d e f : Nat) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']

  -- 結合法則を使う
  rw [← Nat.mul_assoc]
  rw [h]

  -- 結合法則を使う
  rw [Nat.mul_assoc]
