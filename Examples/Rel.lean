import Mathlib.Tactic.GCongr -- `rel` を使用するのに必要

variable (a b c d: Nat)

/-! ## rel -/

-- 不等式を示す例
example (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  rel [h1, h2]

-- 下記で示すように，ゴールが関係式でないときにはエラーになる

/-- error: rel failed, goal not a relation -/
#guard_msgs in
  example (x : Nat) : Nat := by rel [x]

/-! ## gcongr -/

example (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  -- `gcongr` でも示すことができる
  gcongr

/-!
  ## rel の推論

  `rel` は，たとえば整数 `x: Int` に対して `0 ≤ x ^ 2` であることを
  自動的に適用するなど, 多少の推論を行います．
-/

example (x: Int) (h1 : a ≤ b) : x ^ 2 * a ≤ x ^ 2 * b := by
  rel [h1]

example (x: Int) (h1 : a ≤ b) : x ^ 2 * a ≤ x ^ 2 * b := by
  -- これも `gcongr` で示すことができる
  gcongr
