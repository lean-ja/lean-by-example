import Playground.MyNat.C06PartialOrder

/- ## 0 に関する不等式 -/

/-- 任意の自然数はゼロ以上である -/
@[simp, grind =>]
theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  -- `≤`を和の等式に帰着させると、
  rw [MyNat.le_iff_add]

  -- 示すべきことは`∃ k, 0 + k = n`であるが、これは`k = n`とすれば成り立つ
  exists n
  simp

/-- `0`以下の自然数は`0`しかない -/
@[grind →]
theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
  induction n with grind

/-- `0`以下であることと、`0`であることは同値 -/
@[simp, grind =]
theorem MyNat.le_zero {n : MyNat} : n ≤ 0 ↔ n = 0 := by
  grind

/-- 任意の自然数はゼロか正 -/
theorem MyNat.eq_zero_or_pos (n : MyNat) : n = 0 ∨ 0 < n := by
  dsimp [(· < ·)]
  grind

/- ## 広義順序を等式と狭義順序で書き換える -/

@[grind →]
theorem MyNat.eq_or_lt_of_le {m n : MyNat} (h : n ≤ m) : n = m ∨ n < m := by
  dsimp [(· < ·)]
  by_cases heq : n = m <;> grind only [MyNat.le_antisymm]

/-- 狭義順序は広義順序よりも「強い」-/
@[grind →]
theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := by
  dsimp [(· < ·)] at h
  grind

@[grind →]
theorem MyNat.le_of_eq_or_lt {m n : MyNat} (h : n = m ∨ n < m) : n ≤ m := by
  cases h with grind

/-- 広義順序`≤`は等号`=`と狭義順序`<`で書き換えられる -/
theorem MyNat.le_iff_eq_or_lt (m n : MyNat) : n ≤ m ↔ n = m ∨ n < m := by
  constructor <;> grind

/- ## 狭義順序を広義順序と等号で書き換える -/

#see Nat.lt_of_le_of_ne
@[grind →]
theorem MyNat.lt_of_le_of_ne {m n : MyNat} (h : n ≤ m) (neq : n ≠ m) : n < m := by
  induction m with
  | zero => grind
  | succ m ih =>
    dsimp [(· < ·)]
    refine ⟨by assumption, ?_⟩
    intro hle
    grind

@[grind →]
theorem MyNat.le_and_ne_of_lt {m n : MyNat} (h : n < m) : n ≤ m ∧ n ≠ m := by
  dsimp [(· < ·)] at h
  grind

#see Nat.lt_iff_le_and_ne
@[grind =]
theorem MyNat.lt_iff_le_and_ne (m n : MyNat) : n < m ↔ n ≤ m ∧ n ≠ m := by
  constructor <;> grind

@[grind →]
theorem MyNat.add_one_le_of_lt {a b : MyNat} (h : a < b) : a + 1 ≤ b := by
  rw [MyNat.lt_iff_le_and_ne] at h
  obtain ⟨hle, hne⟩ := h
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := hle
  induction k with
  | zero => grind
  | succ k _ =>
    exists k
    rw [← hk]
    ac_rfl

theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
  induction a with grind

@[grind =>]
theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  induction a with grind

open Lean Grind

instance : LinearOrder MyNat where
  le_total := MyNat.le_total
