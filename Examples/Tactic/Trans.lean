/-
# trans
`trans` は、推移律を利用して示すべきことを分割するタクティクです。

推移的な関係 `∼` に対してゴールが `a ∼ c` であるとき、`trans b` により2つのサブゴール `a ∼ b` と `b ∼ c` が生成されます。[`calc`](./Calc.md) を使っても同じことができますが、`calc` を使うまでもないときに便利かもしれません。
-/
import Mathlib.Tactic.Relation.Trans

example {n m : Nat} (h1 : n ≤ 1) (h2 : 1 ≤ m) : n ≤ m := by
  -- 1 を仲介して示す
  trans 1

  · show n ≤ 1
    assumption

  · show 1 ≤ m
    assumption
