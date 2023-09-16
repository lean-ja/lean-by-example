-- ANCHOR: first
example (hPQ: P → Q) (hQR: Q → R) : P → R := by
  -- 示したいことが `P → R` なので，`P` だと仮定する
  intro hP

  -- 仮定 `hPQ : P → Q` と `hP : P` から `Q` が導かれる
  have hQ : Q := by exact hPQ hP

  -- 仮定 `hQR : Q → R` と `hQ : Q` から `R` が導かれる
  exact hQR hQ
-- ANCHOR_END: first


-- ANCHOR: and
example (hPQ: P ∧ Q) : P := by
  -- `P ∧ Q` という仮定を分解する
  have ⟨ hP, hQ ⟩ := hPQ

  assumption
-- ANCHOR_END: and
