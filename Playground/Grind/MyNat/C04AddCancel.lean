import Playground.Grind.MyNat.C03CommSemiring

-- 以降、l m nはすべてMyNat型の項とする
variable {l m n : MyNat}

@[grind =>]
theorem MyNat.add_one_right_cancel (h : l + 1 = n + 1) : l = n := by
  injection h

/-- 右から足す演算`(· + m)`は単射 -/
@[grind =>]
theorem MyNat.add_right_cancel (h : l + m = n + m) : l = n := by
  induction m with grind

/-- 左から足す演算`(l + ·)`は単射 -/
@[grind =>]
theorem MyNat.add_left_cancel (h : l + m = l + n) : m = n := by
  grind

/-- 右からの足し算のキャンセル -/
@[grind =]
theorem MyNat.add_right_cancel_iff : l + m = n + m ↔ l = n := by
  grind

/-- 左からの足し算のキャンセル -/
@[grind =]
theorem MyNat.add_left_cancel_iff : l + m = l + n ↔ m = n := by
  grind

@[grind =>]
theorem MyNat.add_right_eq_self (m n : MyNat) : m + n = m ↔ n = 0 := by
  refine ⟨?_, by grind⟩
  intro h
  have : m + n = m + 0 := by grind
  grind

@[grind =>]
theorem MyNat.add_left_eq_self (m n : MyNat) : n + m = m ↔ n = 0 := by
  grind

@[grind =>]
theorem MyNat.self_eq_add_right (m n : MyNat) : m = m + n ↔ n = 0 := by
  grind

@[grind =>]
theorem MyNat.self_eq_add_left (m n : MyNat) : m = n + m ↔ n = 0 := by
  grind

/-- 和がゼロなら両方がゼロ -/
@[grind =>]
theorem MyNat.eq_zero_of_add_eq_zero : m + n = 0 → m = 0 ∧ n = 0 := by
  intro h
  induction n with
  | zero => grind
  | succ n ih =>
    exfalso
    rw [show m + (n + 1) = m + n + 1 from by ac_rfl] at h
    injection h

@[grind =>]
theorem MyNat.add_eq_zero_of_eq_zero : m = 0 ∧ n = 0 → m + n = 0 := by
  grind

/-- 和がゼロであることと両方がゼロであることは同値 -/
@[grind =]
theorem MyNat.add_eq_zero_iff_eq_zero : m + n = 0 ↔ m = 0 ∧ n = 0 := by
  grind
