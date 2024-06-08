/- # by_cases

`by_cases` は排中律を使って場合分けをするタクティクです．`by_cases h : P` とすると，`P` が成り立つときと成り立たないときのゴールがそれぞれ生成されます．-/
example (P: Prop) : ¬¬P → P := by
  intro hnnP

  -- `P` が成り立つかどうかで場合分けする
  by_cases hP : P

  case pos =>
    -- `P` が成り立つとき
    assumption

  case neg =>
    -- `¬ P` が成り立つとき
    contradiction
