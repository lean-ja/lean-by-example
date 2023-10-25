variable (P Q R : Prop)

-- ANCHOR: first
example (hP: P) (hQ: Q) : P ∧ Q := by
  -- 穴埋め形式で証明を作ることができる
  refine ⟨?_, hQ⟩

  -- ゴールが `⊢ P` になる
  show P

  exact hP
-- ANCHOR_END: first


-- ANCHOR: constructor
example (hP: P) (hQ: Q) (hR : R) : P ∧ Q ∧ R := by
  -- ゴールを３つに分割する
  refine ⟨?_, ?_, ?_⟩

  · show P
    exact hP
  · show Q
    exact hQ
  · show R
    exact hR

-- `constructor` を使った場合
-- 一度に２つのゴールに分割することしかできない
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
-- ANCHOR_END: constructor


variable (P Q : Prop)

-- ANCHOR: apply
example (hPQ : P → Q) (hP : P) : Q := by
  refine hPQ ?_

  -- ゴールが `⊢ P` になる
  show P

  refine hP
-- ANCHOR_END: apply
