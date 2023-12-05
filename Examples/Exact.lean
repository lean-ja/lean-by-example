variable (P Q : Prop)

-- ANCHOR: first
example (hP: P) : P := by
  exact hP
-- ANCHOR_END: first


-- ANCHOR: and
example (hP: P) (hQ: Q) : P ∧ Q := by
  exact ⟨ hP, hQ ⟩
-- ANCHOR_END: and
