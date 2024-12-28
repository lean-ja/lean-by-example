/- # suffices

`suffices` は、数学でよくある「～を示せば十分である」という推論を行うタクティクです。

ゴールが `⊢ P` であるときに `suffices h : Q from` を実行すると、以下が実行されます。

* `suffices h : Q from` のブロック内で、仮定に `h : Q` が追加される。
* `suffices h : Q from` 以降で、ゴールが `⊢ Q` に書き換えられる。

[`apply`](./Apply.md) タクティクと似ていますが、`apply` と違って「十分条件になっていること」の証明が明らかでないときにも使うことができます。-/

example (P : Prop) : ¬ ¬ (P ∨ ¬ P) := by
  intro h

  -- `¬ P` を示せば十分である。
  suffices hyp : ¬ P from by
    -- 仮定に `¬ P` が追加される。
    guard_hyp hyp : ¬ P

    -- このとき、特に `P ∨ ¬ P` が成り立つので、示すべきことが言える。
    have : P ∨ ¬ P := by simp_all
    contradiction

  -- 無事ゴールを `¬ P` に帰着させることができた。
  -- 以下 `¬ P` を示す。
  guard_target =ₛ ¬ P

  intro hP
  have : P ∨ ¬ P := by simp_all
  contradiction

/- ## 構文
`suffices Q from by ...` という構文では、タクティクによって証明を構成するモードになります。`suffices Q from ...` という構文では、証明項を直接構成するモードになります。 -/

example (n : Nat) (h : n ≤ 0) : n = 0 := by
  -- `n = 0` を示すためには、`n ≤ 0` であることを示せば十分である。
  suffices hyp : n ≤ 0 from Nat.eq_zero_of_le_zero h

  -- `n ≤ 0` であることを示す。
  assumption
