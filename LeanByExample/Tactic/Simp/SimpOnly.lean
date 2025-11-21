/-- 0 っぽい何か -/
opaque zero : Nat

/-- １っぽい何か -/
opaque one : Nat

/-- `zero` に右から１を足すと `one` に等しい -/
@[simp] axiom add_zero_one_eq_one : zero + 1 = one

/-- `zero` 同士を足すと `zero` に等しい -/
@[simp] axiom add_zero_zero_eq_zero : zero + zero = zero

example : (zero + zero) + 1 = one := by
  -- 1つだけ使用して単純化を行ってみる
  simp only [add_zero_zero_eq_zero]

  -- まだゴールが残っている
  guard_target =ₛ zero + 1 = one

  simp
