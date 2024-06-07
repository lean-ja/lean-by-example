/- # rfl

`rfl` は，反射的(reflexive)な関係(relation)に対して関係式を示すタクティクです．ここで二項関係 `R : α → α → Prop` が反射的であるとは，任意の `a : α` に対して `R a a` が成り立つことをいいます．

関係 `R` が反射的であることを `rfl` に利用させるには，`R` の反射性を示した定理に `@[refl]` タグを付けます．`@[refl]` で登録された定理を用いるので，追加でライブラリを import することにより示すことができる命題を増やせます． -/
import Mathlib.Tactic -- 大雑把に import する

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

/-! 適宜ライブラリが必要ですが，不等式 `≤` の反射性も登録されているので `rfl` で示すことができます．-/

example (n : ℕ) : n ≤ n := by rfl
