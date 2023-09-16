-- ANCHOR: first
example (hPQ: P → Q) (hQR: Q → R) : P → R := by
  -- 示したいことが `P → R` なので，`P` だと仮定する
  intro hP

  -- 仮定 `hPQ : P → Q` と `hP : P` から `Q` が導かれる
  have hQ : Q := hPQ hP

  -- 仮定 `hQR : Q → R` と `hQ : Q` から `R` が導かれる
  exact hQR hQ
-- ANCHOR_END: first


-- ANCHOR: neg
example (h: P → Q) : ¬Q → ¬P := by
  -- 示したいことが `¬Q → ¬P` なので，`¬Q` だと仮定する
  -- そうするとゴールが `¬P` になるので，
  -- さらに `intro` を行って仮定 `hP : P` を導入する
  intro hnQ hP

  -- `hP : P` と `h : P → Q` から `Q` が導かれる
  have hQ : Q := h hP

  -- `hQ : Q` と `hnQ : ¬Q` から矛盾が導かれる
  contradiction
-- ANCHOR_END: neg