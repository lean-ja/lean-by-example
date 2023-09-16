-- 自明に正しい等式
example : 1 + 1 = 2 := by rfl

-- 変数を含む等式
example (x : Nat) : x = x := by rfl

example (P : Prop) : P = P := by rfl