/- # all_goals

`all_goals` は，後に続くタクティクをすべてのゴールに対して適用します．
-/
variable (P Q : Prop)

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- `P` と `Q` をそれぞれ示せばよい
  constructor

  -- どちらも仮定から従うので，
  -- 両方に `assumption` を適用する
  all_goals assumption

/-! `all_goals` には，タクティクブロックを渡すこともできます．-/

example {R : Prop} (hnP : ¬ P) : (P → R) ∧ (P → Q) := by
  constructor
  all_goals
    intro h
    contradiction

/-!
## タクティク結合子 `<;>`
タクティク結合子 `<;>` によってもほぼ同じことができます．
-/

example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> assumption

/-! しかし, `<;>` と `all_goals` は完全に同じではありません．
`<;>` が「直前のタクティクによって生成された全てのサブゴール」に対して後続のタクティクを実行するのに対して，`all_goals` は「すべての未解決のゴール」に対して後続のタクティクまたはタクティクブロックを実行します．

実際に以下のような例ではその違いが現れます．
-/

variable (P Q R : Prop)

example (hP : P) (hQ : Q) (hR : R) : (P ∧ Q) ∧ R := by
  constructor

  constructor <;> try assumption

  -- まだ示すべきことが残っている
  show R
  assumption

example (hP : P) (hQ : Q) (hR : R) : (P ∧ Q) ∧ R := by
  constructor

  constructor
  all_goals
    try assumption

  -- 証明完了
  done
