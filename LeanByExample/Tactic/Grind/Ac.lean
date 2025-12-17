
/-- 自然数をイメージした何か -/
opaque MyNat : Type

variable [Add MyNat]

/-- 加法の結合法則 -/
axiom MyNat.add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c)

/-- 結合法則が成り立つことを型クラス経由で登録する -/
instance : @Std.Associative MyNat (· + ·) :=
  ⟨MyNat.add_assoc⟩

example (a b c d : MyNat) : (a + b) + (c + d) = a + (b + c) + d := by
  -- ac ソルバーを無効にすると証明できない
  fail_if_success grind -ac

  -- grind で証明することができる
  grind only


/-- 加法の交換法則 -/
axiom MyNat.add_comm (a b : MyNat) : a + b = b + a

/-- 交換法則が成り立つことを型クラス経由で登録する -/
instance : @Std.Commutative MyNat (· + ·) :=
  ⟨MyNat.add_comm⟩

example (a b c : MyNat) : a + b + c = c + b + a := by
  -- ac ソルバーを無効にすると証明できない
  fail_if_success grind -ac

  -- grind で証明することができる
  grind only
