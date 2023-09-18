import Mathlib.Tactic.Ring


-- ANCHOR: first
example (hPQ: P → Q) (hQR: Q → R) : P → R := by
  -- 示したいことが `P → R` なので，`P` だと仮定する
  intro hP

  -- 仮定 `hPQ : P → Q` と `hP : P` から `Q` が導かれる
  have hQ : Q := by exact hPQ hP

  -- 仮定 `hQR : Q → R` と `hQ : Q` から `R` が導かれる
  exact hQR hQ
-- ANCHOR_END: first


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


-- ANCHOR: and
example (hPQ: P ∧ Q) : P := by
  -- `P ∧ Q` という仮定を分解する
  -- `hQ: Q` は不要なのでアンダースコアに置き換える
  have ⟨ hP, _ ⟩ := hPQ

  assumption
-- ANCHOR_END: and
