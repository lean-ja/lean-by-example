variable (P Q R : Prop)

-- ANCHOR: first
example (hPQ: P → Q) (hQR: Q → R) : P → R := by
  -- 示したいことが `P → R` なので，`P` だと仮定する
  intro hP

  -- `R` を示したい
  show R

  -- 仮定 `hPQ : P → Q` と `hP : P` から `Q` が導かれる
  have hQ : Q := hPQ hP

  -- 仮定 `hQR : Q → R` と `hQ : Q` から `R` が導かれる
  exact hQR hQ
-- ANCHOR_END: first


-- ANCHOR: forall
example (P Q : Nat → Prop) (h : ∀ n, P n ↔ Q n) : ∀ y, P (y + 1) → Q (y + 1) := by
  -- 任意の `y` について示すので，`intro` で `y` を導入する
  -- そして `P (y + 1) → Q(y + 1)` を示したいので，`P (y + 1)` を仮定する
  intro y hyP

  -- `Q (y + 1)` を示せば良い
  show Q (y + 1)

  -- 同値を使ってゴールを書き換える
  rw [← h]

  -- 仮定 `P (y + 1)` より従う
  assumption
-- ANCHOR_END: forall


-- ANCHOR: neg
example (h: P → Q) : ¬Q → ¬P := by
  -- 示したいことが `¬Q → ¬P` なので，`¬Q` だと仮定する
  -- そうするとゴールが `¬P` になるので，
  -- さらに `intro` を行って仮定 `hP : P` を導入する
  intro hnQ hP

  -- 矛盾を示したい
  show False

  -- `hP : P` と `h : P → Q` から `Q` が導かれる
  have hQ : Q := h hP

  -- `hQ : Q` と `hnQ : ¬Q` から矛盾が導かれる
  contradiction
-- ANCHOR_END: neg
