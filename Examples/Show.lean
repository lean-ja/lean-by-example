example (hP: P) (hQ: Q) : P ∧ Q := by
  constructor
  · show P
    exact hP
  · show Q
    exact hQ