/- # refine

`refine` は [`exact`](./Exact.md) タクティクと同様に機能しますが、メタ変数(`?` から始まる変数で、プレースホルダとして機能する)を受け入れて新しいゴールを生成するという違いがあります。 -/

example {P Q : Prop} (hP : P) (hQ : Q) : P ∧ Q := by
  -- 穴埋め形式で証明を作ることができる
  refine ⟨?_, hQ⟩

  -- ゴールが `⊢ P` になる
  show P

  exact hP

/- ## 用途

`refine` はかなり一般的なタクティクであり、様々な場面で使うことができます。

### constructor の一般化として

`refine` は [`constructor`](./Constructor.md) の代わりに使うこともできます。実際 `refine` は `constructor` よりも柔軟で、`⊢ P ∧ Q ∧ R` のような形のゴールは `constructor` よりも簡潔に分割できます。-/

example {P Q R : Prop} (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := by
  -- ゴールを３つに分割する
  refine ⟨?_, ?_, ?_⟩

  · exact hP
  · exact hQ
  · exact hR

/- `constructor` を使った場合、一度に２つのゴールに分割することしかできません。 -/

example {P Q R : Prop} (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := by
  constructor
  · exact hP
  · constructor
    · exact hQ
    · exact hR

/- ### apply の一般化として

`h : P → Q` という命題があって、ゴールが `⊢ Q` であるとき `refine h ?_` は `apply h` と同様に機能するので、`refine` で [`apply`](./Apply.md) を代用することができます。 -/

example {P Q : Prop} (hPQ : P → Q) (hP : P) : Q := by
  refine hPQ ?_

  -- ゴールが `⊢ P` になる
  show P

  refine hP

/- ### 自明なケースを示す

ゴールが `⊢ P ∧ Q` であり、`P` が成り立つことが自明であった場合、いちいち `⊢ P` と `⊢ Q` の２つのサブゴールを作って示すのは面倒に思えます。こうしたとき、`refine` を使うとサブゴールを生成せずにゴールを単に `⊢ Q` に変えることができます。
-/

example {P Q : Prop} (hP : P) (hQ : ¬ P ∨ Q) : P ∧ Q := by
  -- `P` が成り立つのは自明なので、`Q` だけ示せばよい
  refine ⟨by assumption, ?_⟩

  -- ゴールが `⊢ Q` になる
  guard_target =ₛ Q

  simp_all

/- ### 場合分けの他の枝で示したことを再利用する

メタ変数を使って、場合分けの他の枝で示したことを再利用することができます。
-/

example {P Q : Prop} (h1 : P → Q) (h2 : P → Q → False) (hP : P) : False := by
  refine h2 ?a ?_ -- `?a` は `P` の証明を要求するメタ変数
  · exact hP
  · exact h1 ?a -- `?a` を `P` の証明の代替として使うことができる
