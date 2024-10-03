/- # exact

ゴールが `P` で、ローカルコンテキストに `hP : P` があるときに、`exact hP` はゴールを閉じます。`hP` がゴールの証明になっていないときには、失敗してエラーになります。-/
variable (P Q : Prop)

example (hP : P) (hQ : Q) : P := by
  -- `hQ : Q` は `P` の証明ではないのでもちろん失敗する
  fail_if_success exact hQ

  exact hP

/-! `exact` は与えられた証明項をそのまま証明として使うタクティクなので、`by exact` だけで証明が終わるときには、`by exact` を消しても証明が通ります。-/

example (hP : P) (hQ : Q) : P ∧ Q := by
  exact And.intro hP hQ

example (hP : P) (hQ : Q) : P ∧ Q := And.intro hP hQ

/- なお `And` は[構造体](../Declarative/Structure.md)なので[無名コンストラクタ](../Declarative/Structure.md#AnonymousConstructor)記法を用いて次のように書くこともできます。-/

example (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩

/- ## assumption との関連

`exact` は常にどの命題を使うか明示する必要がありますが、「ゴールを `exact` で閉じることができるような命題をローカルコンテキストから自動で探す」 [`assumption`](./Assumption.md) というタクティクもあります。-/
