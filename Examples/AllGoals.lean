variable (P Q : Prop)

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- `P` と `Q` をそれぞれ示せばよい
  constructor

  -- どちらも仮定から従うので，
  -- 両方に `assumption` を適用する
  all_goals
    assumption
