import Playground.MyNat.C01AddAssoc

/-- `MyNat`についての掛け算 -/
def MyNat.mul (m n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => MyNat.mul m n + m

/-- `MyNat`の掛け算を`*`で表せるように、型クラス`Mul`のインスタンスにする -/
instance : Mul MyNat where
  mul := MyNat.mul

/-- 右から`0`を乗算しても`0` -/
@[grind =, simp]
theorem MyNat.mul_zero (m : MyNat) : m * 0 = 0 := by
  rfl

/-- 右のオペランドにある`· + 1`の消去 -/
@[grind =]
theorem MyNat.mul_add_one (m n : MyNat) : m * (n + 1) = m * n + m := by
  rfl

/-- 左のオペランドにある`· + 1`の消去 -/
@[grind =]
theorem MyNat.add_one_mul (m n : MyNat) : (m + 1) * n = m * n + n := by
  induction n with grind

/-- 左から`0`を乗算しても`0` -/
@[grind =, simp]
theorem MyNat.zero_mul (n : MyNat) : 0 * n = 0 := by
  induction n with grind

/-- 右から`1`を掛けても変わらない -/
@[grind =, simp]
theorem MyNat.mul_one (n : MyNat) : n * 1 = n := by
  induction n with grind

/-- 左から`1`を掛けても変わらない -/
@[grind =, simp]
theorem MyNat.one_mul (n : MyNat) : 1 * n = n := by
  induction n with grind

/-- 掛け算の交換法則 -/
@[grind _=_]
theorem MyNat.mul_comm (m n : MyNat) : m * n = n * m := by
  induction n with grind

/-- 右から掛けたときの分配法則 -/
@[grind _=_]
theorem MyNat.add_mul (l m n : MyNat) : (l + m) * n = l * n + m * n := by
  induction n with grind

/-- 左から掛けたときの分配法則 -/
@[grind _=_]
theorem MyNat.mul_add (l m n : MyNat) : l * (m + n) = l * m + l * n := by
  grind

/-- 掛け算の結合法則 -/
@[grind _=_]
theorem MyNat.mul_assoc (l m n : MyNat) : l * m * n = l * (m * n) := by
  induction n with grind

-- 掛け算の結合法則を登録する
instance : Std.Associative (α := MyNat) (· * ·) where
  assoc := MyNat.mul_assoc

-- 掛け算の交換法則を登録する
instance : Std.Commutative (α := MyNat) (· * ·) where
  comm := MyNat.mul_comm
