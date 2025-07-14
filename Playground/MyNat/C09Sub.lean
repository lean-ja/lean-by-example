import Playground.MyNat.C08LinearOrder

/- ## 引き算の定義 -/

#see Nat.pred
/-- MyNatの前者(predecessor)を返す関数 -/
def MyNat.pred (n : MyNat) :=
  match n with
  | 0 => 0
  | n + 1 => n

@[simp, grind =]
theorem MyNat.pred_zero : MyNat.pred 0 = 0 := by
  rfl

@[simp, grind =]
theorem MyNat.pred_succ (n : MyNat) : MyNat.pred (n + 1) = n := by
  rfl

#see Nat.sub
def MyNat.sub (m n : MyNat) :=
  match m, n with
  | m, 0 => m
  | m, n + 1 => pred (.sub m n)

instance : Sub MyNat where
  sub := MyNat.sub

/- ## 引き算が足し算とキャンセルすること -/

@[simp, grind =]
theorem MyNat.pred_eq_sub_one (n : MyNat) : MyNat.pred n = n - 1 := by
  rfl

#see Nat.sub_zero
@[simp, grind =]
theorem MyNat.sub_zero (n : MyNat) : n - 0 = n := by rfl

#see Nat.sub_succ
@[grind _=_]
theorem MyNat.sub_succ (m n : MyNat) : m - (n + 1) = MyNat.pred (m - n) := by
  rfl

@[simp, grind =]
theorem MyNat.zero_sub (n : MyNat) : 0 - n = 0 := by
  induction n with grind

#see Nat.add_sub_self_left
@[simp, grind =]
theorem MyNat.add_sub_self_left (n m : MyNat) : (n + m) - n = m := by
  induction n generalizing m with grind

@[simp, grind =]
theorem MyNat.add_sub_self_right (m n : MyNat) : (n + m) - m = n := by
  grind

@[simp, grind =]
theorem MyNat.sub_self_zero (n : MyNat) : n - n = 0 := by
  have := MyNat.add_sub_self_left n 0
  grind

/- ## 引き算と足し算の関係 -/

@[grind _=_]
theorem MyNat.sub_add_one (n m : MyNat) : n - (m + 1) = (n - m) - 1 := by
  grind

@[grind _=_]
theorem MyNat.sub_add (n m k : MyNat) : n - (m + k) = (n - m) - k := by
  induction k with grind

/- ## 引き算と掛け算の分配法則 -/

@[grind _=_]
theorem MyNat.sub_one_mul (n k : MyNat) : (n - 1) * k = n * k - 1 * k := by
  induction n with grind

#see Nat.sub_mul
@[grind _=_]
theorem MyNat.sub_mul (m n k : MyNat) : (n - m) * k = n * k - m * k := by
  induction m with grind
