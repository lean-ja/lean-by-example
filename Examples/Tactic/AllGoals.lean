/-! # all_goals

`all_goals` は，すべてのゴールに対して共通のタクティクを適用します．
-/
variable (P Q : Prop)

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- `P` と `Q` をそれぞれ示せばよい
  constructor

  -- どちらも仮定から従うので，
  -- 両方に `assumption` を適用する
  all_goals
    assumption

/-! `<;>` によっても同じことができます．-/

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> assumption
