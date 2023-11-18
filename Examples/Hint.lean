import Mathlib.Tactic -- `hint` は検索を伴うので，おおざっぱに import している

-- `says` のチェックをCIで無効にする
set_option says.no_verify_in_CI true

variable (P Q R : Prop) (a b : ℕ)

/-! # hint -/

example (h : 1 < 0) : False := by
  hint says
    linarith

example (p : P) (h : P → Q) : Q := by
  hint says
    exact h p

example (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by
  hint says
    simp_all only [and_self]

example (h : a < b) : ¬ b < a := by
  hint says
    linarith

example : 37^2 - 35^2 = 72 * 2 := by
  hint says
    exact rfl

example : Nat.Prime 37 := by
  hint says
    exact (Nat.prime_iff_card_units 37).mpr rfl

/-!
  ## タクティクの新規登録
  `register_hint tac` で `tac` を使うように設定できます．
-/

register_hint nlinarith

example (h : a ≤ b) : (a + b) ^ 2 ≤ 4 * b ^ 2 := by
  hint says
    nlinarith
