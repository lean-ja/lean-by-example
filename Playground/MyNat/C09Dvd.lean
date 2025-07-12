import Playground.MyNat.C08Sub

/- ## 整除関係の推移律まで -/

#see Nat.instDvd
/-- MyNat 上の整除関係 -/
instance : Dvd MyNat where
  dvd a b := ∃ c : MyNat, b = a * c

#see Nat.dvd_refl
/-- 整除関係の反射律 -/
@[refl, simp, grind <=]
theorem MyNat.dvd_refl (n : MyNat) : n ∣ n := by
  exists 1
  simp

@[simp, grind <=]
theorem MyNat.dvd_zero (n : MyNat) : n ∣ 0 := by
  exists 0

#see Nat.dvd_mul_left
@[grind <=, simp]
theorem MyNat.dvd_mul_left (m n : MyNat) : m ∣ n * m := by
  exists n
  ac_rfl

@[grind <=, simp]
theorem MyNat.dvd_mul_right (m n : MyNat) : m ∣ m * n := by
  exists n

#see Nat.dvd_trans
/- 整除関係の推移律 -/
@[grind →]
theorem MyNat.dvd_trans {a b c : MyNat} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  obtain ⟨d, hd⟩ := h₁
  obtain ⟨e, he⟩ := h₂
  grind -- **TODO** `exists` タクティクを使用していないのにゴールを閉じることができる

/- 整除関係を「推移的な二項関係」として登録する -/
instance : Trans (· ∣ · : MyNat → MyNat → Prop) (· ∣ ·) (· ∣ ·) where
  trans := MyNat.dvd_trans

/- ## 1 を割り切る数は 1 しかない -/

@[grind =>] -- **TODO**: `grind` が非常に強力過ぎて、証明を理解できない例
theorem MyNat.le_one_iff_eq_zero_or_eq_one (n : MyNat) : n ≤ 1 ↔ n = 0 ∨ n = 1 := by
  constructor <;> grind

@[simp↓, grind =]
theorem MyNat.mul_eq_one_iff (m n : MyNat) : m * n = 1 ↔ m = 1 ∧ n = 1 := by
  refine ⟨?_, by grind⟩
  induction m with grind

#see Nat.dvd_one
@[simp, grind =]
theorem MyNat.dvd_one (n : MyNat) : n ∣ 1 ↔ n = 1 := by
  refine ⟨?_, by grind⟩
  intro h
  obtain ⟨c, hc⟩ := h
  grind
