import Mathlib.Algebra.Algebra.Basic -- `not_lt` などが使えるようにする

/- ## contradiction -/

-- `False`
example (h : False) : P := by contradiction

-- 明らかに偽な等式
example (h : 2 + 2 = 3) : P := by contradiction

-- 明らかに偽な等式
example (x : Nat) (h : x ≠ x) : P := by contradiction

-- 矛盾する仮定
example (hP : P) (hnP : ¬ P) : Q := by contradiction

/- ## contradiction が通りそうで通らない例 -/

variable (n m : ℕ)

example (hl : n ≤ m) (hg : m < n) : False := by
  -- 明らかに矛盾に見えるが， 通らない
  try contradiction

  -- 通らない理由は， `n ≤ m` が `¬ m < n` を意味することを
  -- `contradiction` は知らないから．

  -- 次のようにして教えてあげると…
  have := hl.not_lt

  -- `contradiction` が通るようになる
  contradiction
