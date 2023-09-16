-- ANCHOR: first
/-- `P → Q` かつ `P` ならば `Q` -/
example (h: P → Q) (hP: P) : Q := by
  -- ゴールが `P` に変わる
  apply h

  exact hP
-- ANCHOR_END: first


-- ANCHOR: exact
/-- `P → Q` かつ `P` ならば `Q` -/
example (h: P → Q) (hP: P) : Q := by
  exact h hP
-- ANCHOR_END: exact


-- ANCHOR: not
/-- 矛盾 -/
example (hn: ¬ P) (hP: P) : False := by
  -- ゴールが `P` に変わる
  apply hn

  exact hP
-- ANCHOR_END: not


-- ANCHOR: alt
/-- `P → Q` かつ `P` ならば `Q` -/
example (h: P → Q) (hP: P) : Q := by
  apply h
  apply hP
-- ANCHOR_END: alt