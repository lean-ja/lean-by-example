variable (P Q : Prop)

-- ANCHOR: first
example (hP: P) (hQ: Q) : P ∧ Q := by
  -- 穴埋め形式で証明を作ることができる
  refine ⟨?_, hQ⟩

  -- ゴールが `⊢ P` になる
  show P

  exact hP
-- ANCHOR_END: first
