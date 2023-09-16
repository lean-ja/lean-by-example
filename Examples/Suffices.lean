example (hPQ: P → Q) (hQR: Q → R) (hP: P) : R := by
  -- `Q` を示せば十分
  suffices Q from hQR this

  exact hPQ hP