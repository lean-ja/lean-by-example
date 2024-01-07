import Mathlib.Tactic -- `hint` は検索を伴うので，おおざっぱに import している

variable (P Q R : Prop) (a b : ℕ)

/-! # hint -/

example (h : 1 < 0) : False := by
  -- linarith
  hint

example (p : P) (h : P → Q) : Q := by
  -- exact h p
  hint

example (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by
  -- simp_all only [and_self]
  hint

example (h : a < b) : ¬ b < a := by
  -- linarith
  hint

example : 37^2 - 35^2 = 72 * 2 := by
  -- exact rfl
  hint

example : Nat.Prime 37 := by
  -- exact (Nat.prime_iff_card_units 37).mpr rfl
  hint

/-!
  ## タクティクの新規登録
  `register_hint tac` で `tac` を使うように設定できます．
-/

register_hint nlinarith

example (h : a ≤ b) : (a + b) ^ 2 ≤ 4 * b ^ 2 := by
  -- nlinarith
  hint
