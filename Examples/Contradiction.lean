-- `False`
example (h : False) : P := by contradiction

-- 明らかに偽な等式
example (h : 2 + 2 = 3) : P := by contradiction

-- 明らかに偽な等式
example (x : Nat) (h : x ≠ x) : P := by contradiction

-- 矛盾する仮定
example (hP : P) (hnP : ¬ P) : Q := by contradiction
