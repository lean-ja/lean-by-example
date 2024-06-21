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

/- ## 補足
2項関係 `(· ≡ ·) : A → A → Prop` の反射性とは，任意の `a : A` に対して `a ≡ a` が成り立つという性質です．反射性を使って何かを示すと言っても，`a ≡ a` という形の命題しか示せないのではないかという気がするかもしれません．しかし実際には `rfl` は定義に従って項の簡約を行うため，`a` と `b` が定義上等しいものであれば `a ≡ b` を `rfl` で示すことができます．
-/

-- 簡約すると3になる
/-- info: 3 -/
#guard_msgs in #reduce (2 ^ 30 + 3 ^ 30) % 5

example : (2 ^ 30 + 3 ^ 30) % 5 = 3 := by rfl
