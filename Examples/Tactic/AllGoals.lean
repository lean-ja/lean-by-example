/- # all_goals

`all_goals` は、後に続くタクティクをすべてのゴールに対して適用します。
-/
variable (P Q : Prop)

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- `P` と `Q` をそれぞれ示せばよい
  constructor

  -- どちらも仮定から従うので、
  -- 両方に `assumption` を適用する
  all_goals assumption

/- `all_goals` には、タクティクブロックを渡すこともできます。-/

example {R : Prop} (hnP : ¬ P) : (P → R) ∧ (P → Q) := by
  constructor
  all_goals
    intro h
    contradiction

/- タクティク結合子 [`<;>`](./SeqFocus.md) によってもほぼ同じことができます。-/

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> assumption
