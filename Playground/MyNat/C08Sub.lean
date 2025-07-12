import Playground.MyNat.C07LinearOrder

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

#see Nat.sub_zero
@[simp, grind =]
theorem MyNat.sub_zero (n : MyNat) : n - 0 = n := by rfl

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
