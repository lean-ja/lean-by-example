/- # guard_hyp

`guard_hyp` は，ローカルコンテキストにある命題を確認するタクティクです．指定した仮定が存在すれば成功し，そうでなければ失敗します．

通常の証明で使うことはあまりないかもしれません．このタクティクリストでは，ローカルコンテキストの変化を説明するために使用することがあります． -/
import Std.Tactic.GuardExpr -- `guard_hyp` を使うために必要

variable (P : Prop)

example (hP : P) : P := by
  -- 現在ローカルコンテキストにある命題を確認できる
  guard_hyp hP : P

  exact hP
