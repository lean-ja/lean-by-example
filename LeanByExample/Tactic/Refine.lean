/- # refine

`refine` は [`exact`](./Exact.md) タクティクと同様に機能しますが、プレースホルダを受け入れて新しいゴールを生成するという違いがあります。 -/
variable (P Q R : Prop)

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- 穴埋め形式で証明を作ることができる
  refine ⟨?_, hQ⟩

  -- ゴールが `⊢ P` になる
  show P

  exact hP

/- ## 用途

`refine` はかなり一般的なタクティクなので、様々な場面で使うことができます。

### constructor の一般化として

`refine` は [`constructor`](./Constructor.md) の代わりに使うこともできます。実際 `refine` は `constructor` よりも柔軟で、`⊢ P ∧ Q ∧ R` のような形のゴールは `constructor` よりも簡潔に分割できます。-/

example (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := by
  -- ゴールを３つに分割する
  refine ⟨?_, ?_, ?_⟩

  · exact hP
  · exact hQ
  · exact hR

/- `constructor` を使った場合、一度に２つのゴールに分割することしかできません。 -/

example (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := by
  constructor
  · exact hP
  · constructor
    · exact hQ
    · exact hR

/- ### apply の一般化として

`h : P → Q` という命題があって、ゴールが `⊢ Q` であるとき `refine h ?_` は `apply h` と同様に機能するので、`refine` で [`apply`](./Apply.md) を代用することができます。 -/

variable (P Q : Prop)

example (hPQ : P → Q) (hP : P) : Q := by
  refine hPQ ?_

  -- ゴールが `⊢ P` になる
  show P

  refine hP

/- ### 自明なケースを示す

ゴールが `⊢ P ∧ Q` であり、`P` が成り立つことが自明であった場合、いちいち `⊢ P` と `⊢ Q` の２つのサブゴールを作って示すのは面倒に思えます。こうしたとき、`refine` を使うとサブゴールを生成せずにゴールを単に `⊢ Q` に変えることができます。
-/

example (hP : P) (hQ : ¬ P ∨ Q) : P ∧ Q := by
  -- `P` が成り立つのは自明なので、`Q` だけ示せばよい
  refine ⟨by assumption, ?_⟩

  -- ゴールが `⊢ Q` になる
  guard_target =ₛ Q

  simp_all
