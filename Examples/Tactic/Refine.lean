/- # refine

`refine` は `exact` と同様に機能しますが，プレースホルダを受け入れて新しいゴールを生成するという違いがあります． -/
variable (P Q R : Prop)

example (hP: P) (hQ: Q) : P ∧ Q := by
  -- 穴埋め形式で証明を作ることができる
  refine ⟨?_, hQ⟩

  -- ゴールが `⊢ P` になる
  show P

  exact hP

/-! ## constructor との関連

`refine` は [constructor](./Constructor.md) の代わりに使うこともできます．実際 `refine` は `constructor` よりも柔軟で，`⊢ P ∧ Q ∧ R` のような形のゴールは `constructor` よりも簡潔に分割できます．-/

example (hP: P) (hQ: Q) (hR : R) : P ∧ Q ∧ R := by
  -- ゴールを３つに分割する
  refine ⟨?_, ?_, ?_⟩

  · show P
    exact hP
  · show Q
    exact hQ
  · show R
    exact hR

/-! `constructor` を使った場合, 一度に２つのゴールに分割することしかできません． -/

example (hP: P) (hQ: Q) (hR : R) : P ∧ Q ∧ R := by
  constructor
  · show P
    exact hP
  · show Q ∧ R
    constructor
    · show Q
      exact hQ
    · show R
      exact hR

/-! ## apply との関連

`h : P → Q` という命題があって，ゴールが `⊢ Q` であるとき `refine h ?_` は `apply h` と同様に機能するので，`refine` で [apply](./Apply.md) を代用することができます． -/

variable (P Q : Prop)

example (hPQ : P → Q) (hP : P) : Q := by
  refine hPQ ?_

  -- ゴールが `⊢ P` になる
  show P

  refine hP
