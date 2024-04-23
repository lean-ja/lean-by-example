/- # rfl

`rfl` は，`refl attribute` の付けられた定理を用いて関係の反射性(reflexivity)を示すタクティクです．

`@[refl]` で登録された定理を用いるので，追加でライブラリを import することにより示すことができる命題を増やせます． -/
import Mathlib.Init.Data.Nat.Lemmas -- `n ≤ n` を示すために必要
import Mathlib.Tactic.Relation.Rfl

universe u

-- `MyEq` という二項関係を定義する
inductive MyEq {α : Type u} : α → α → Prop
  | refl (a : α) : MyEq a a

example (n : ℕ) : MyEq n n := by
  -- `rfl` で示すことはできない．
  fail_if_success rfl

  apply MyEq.refl

-- `MyEq` が反射的であることを登録する
attribute [refl] MyEq.refl

-- `rfl` で示せるようになる
example (n : ℕ) : MyEq n n := by rfl

/-! ## ≤ と rfl

適宜ライブラリが必要ですが，不等式 `≤` の反射性も登録されているので `rfl` で示すことができます．
-/

example (n : ℕ) : n ≤ n := by rfl

/-! ## 補足

実は `Mathlib.Tactic.Relation.Rfl` を import するかどうかにより，内部で呼び出されるタクティクが変わります．

* `Mathlib.Tactic.Relation.Rfl` ありなら [Lean.MVarId.rfl](https://leanprover-community.github.io/mathlib4_docs//Mathlib/Tactic/Relation/Rfl.html#Lean.MVarId.rfl) が，
* なしなら [Lean.MVarId.refl](https://leanprover-community.github.io/mathlib4_docs//Lean/Meta/Tactic/Refl.html#Lean.MVarId.refl) が

それぞれ参照されます．後者は `@[refl]` が付けられた一般の関係の反射性にアクセスできず，等号 `=` の反射性しか使うことができません．

後者の場合 `rfl` は，単に定義から等しいものが等しいことを示すタクティクになります．-/
