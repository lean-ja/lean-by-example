-- ANCHOR: first
/-- `P → Q` かつ `P` ならば `Q` -/
example (h: P → Q) (hp: P) : Q := by
  -- ゴールが `P` に変わる
  apply h

  exact hp
-- ANCHOR_END: first


-- ANCHOR: exact
/-- `P → Q` かつ `P` ならば `Q` -/
example (h: P → Q) (hp: P) : Q := by
  exact h hp
-- ANCHOR_END: exact


-- ANCHOR: not
/-- 矛盾 -/
example (hn: ¬ P) (hp: P) : False := by
  -- ゴールが `P` に変わる
  apply hn

  exact hp
-- ANCHOR_END: not


-- ANCHOR: alt
/-- `P → Q` かつ `P` ならば `Q` -/
example (h: P → Q) (hp: P) : Q := by
  apply h
  apply hp
-- ANCHOR_END: alt