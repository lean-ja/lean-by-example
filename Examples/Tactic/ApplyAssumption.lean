/- # apply_assumption
`apply_assumption` は，ゴールが `⊢ head` であるときに，`... → ∀ _, ... → head` という形の命題をローカルコンテキストから探し，それを用いてゴールを書き換えます．
-/
variable (P Q R : Prop)

example (hPQ : P → Q) : ¬ Q → ¬ P := by
  intro hQn hP

  -- 矛盾を示したい
  show False

  -- 自動で `hQn` を適用
  apply_assumption
  show Q

  -- 自動で `hPQ` を適用
  apply_assumption
  show P

  -- 自動で `hP` を適用
  apply_assumption

  -- 証明終わり
  done

/-! タクティクを繰り返すことを指示するタクティク [`repeat`](./Repeat.md) と組み合わせると，「ローカルコンテキストにある仮定を適切に選んで `apply`, `exact` することを繰り返し，ゴールを閉じる」ことができます．
-/

example (hPQ : P → Q) (hQR : Q → R) (hQ : P) : R := by
  repeat apply_assumption
