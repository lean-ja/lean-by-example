import Playground.MyNat.C05Preorder

/- # MyNat が PartialOrder であることを示す -/

/- ## 順序関係を足し算で置き換える -/

variable {m n k : MyNat}

/-- `a ≤ b`から和の等式を導く -/
@[grind <=]
theorem MyNat.le.dest (h : n ≤ m) : ∃ k, n + k = m := by
  induction h with
  | refl => exists 0
  | @step l h ih =>
    obtain ⟨k, ih⟩ := ih
    exists k + 1
    grind

@[grind ←]
theorem MyNat.le_add_right (n m : MyNat) : n ≤ n + m := by
  induction m with grind

/-- 和の等式から`a ≤ b`を導く -/
@[grind =>]
theorem MyNat.le.intro (h : n + k = m) : n ≤ m := by
  induction k with grind

/-- 順序関係`n ≤ m`を足し算で書き換える -/
theorem MyNat.le_iff_add : n ≤ m ↔ ∃ k, n + k = m := by
  constructor <;> grind

/- ## PartialOrder -/

@[simp, grind =>]
theorem MyNat.zero_ne_one : 0 ≠ 1 := by
  intro h
  injection h

@[grind =>, simp]
theorem MyNat.not_add_one_le_self (n : MyNat) : ¬ (n + 1 ≤ n) := by
  intro h
  rw [MyNat.le_iff_add] at h
  obtain ⟨k, hk⟩ := h
  rw [show (n + 1) + k = n + (1 + k) from by ac_rfl] at hk
  grind

theorem MyNat.le_antisymm (h1 : n ≤ m) (h2 : m ≤ n) : n = m := by
  induction h1 with grind

open Lean Grind

instance : PartialOrder MyNat where
  le_antisymm := MyNat.le_antisymm
