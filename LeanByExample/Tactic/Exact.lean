/- # exact

ゴールが `P` で、ローカルコンテキストに `hP : P` があるときに、`exact hP` はゴールを閉じます。`hP` がゴールの証明になっていないときには、失敗してエラーになります。-/
set_option linter.unusedVariables false in --#

example {P Q : Prop}(hP : P)(hQ : Q) : P := by
  -- `hQ : Q` は `P` の証明ではないのでもちろん失敗する
  fail_if_success exact hQ

  exact hP

/- `exact` は与えられた証明項をそのまま証明として使うタクティクなので、`by exact` だけで証明が終わるときには、`by exact` を消しても証明が通ります。-/
section
  /- ## by exact の省略ができるケース -/

  variable {P Q : Prop}

  example (hP : P) (hQ : Q) : P ∧ Q := by
    -- exact を使う証明
    exact And.intro hP hQ

  example (hP : P) (hQ : Q) : P ∧ Q :=
    -- by exact を使わない証明
    And.intro hP hQ
end
/- なお `And` は[構造体](#{root}/Declarative/Structure.md)なので[無名コンストラクタ](#{root}/Syntax/AnonymousConstructor.md)記法を用いて次のように書くこともできます。-/

example {P Q : Prop} (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩

/- ## assumption との関連

`exact` は常にどの命題を使うか明示する必要がありますが、「ゴールを `exact` で閉じることができるような命題をローカルコンテキストから自動で探す」 [`assumption`](./Assumption.md) というタクティクもあります。-/
