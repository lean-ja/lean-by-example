/-- 偶数であることを表す帰納的述語 -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | step (n : Nat) : Even n → Even (n + 2)

set_option warn.sorry false

/- ## grind cases -/

example (h : Even 3) : False := by
  fail_if_success grind
  sorry

attribute [grind cases] Even

example (h : Even 3) : False := by
  grind

/- ## grind intro -/

example : Even 0 := by
  fail_if_success grind
  sorry

attribute [grind intro] Even

example : Even 0 := by
  grind

example {m : Nat} (h : Even m) : Even (m + 2) := by
  grind

example (n : Nat) (h : Even n) : ¬ Even (n + 1) := by
  induction n with grind
