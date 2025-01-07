/- # rfl

`rfl` は、反射的(reflexive)な関係に対して関係式を示すタクティクです。ここで二項関係 `R : α → α → Prop` が反射的であるとは、任意の `a : α` に対して `R a a` が成り立つことをいいます。

関係 `R` が反射的であることを `rfl` に利用させるには、`R` の反射性を示した定理に `@[refl]` タグを付けます。-/

universe u

-- `MyEq` という二項関係を定義する
inductive MyEq {α : Type u} : α → α → Prop
  | refl (a : α) : MyEq a a

example (n : Nat) : MyEq n n := by
  -- `rfl` で示すことはできない。
  fail_if_success rfl

  apply MyEq.refl

-- `MyEq` が反射的であることを登録する
attribute [refl] MyEq.refl

-- `rfl` で示せるようになる
example (n : Nat) : MyEq n n := by rfl

/- ## 補足
2項関係 `(· ≡ ·) : A → A → Prop` の反射性とは、任意の `a : A` に対して `a ≡ a` が成り立つという性質です。反射性を使って何かを示すと言っても、`a ≡ a` という形の命題しか示せないのではないかという気がするかもしれません。しかし実際には `rfl` は定義に従って項の簡約を行うため、`a` と `b` が定義上等しいものであれば `a ≡ b` を `rfl` で示すことができます。
-/

-- 簡約すると3になる
/-- info: 3 -/
#guard_msgs in #reduce (2 ^ 30 + 3 ^ 30) % 5

example : (2 ^ 30 + 3 ^ 30) % 5 = 3 := by rfl

/- もし反射的でない関係について「定義から計算して示す」ことが必要であれば、[`decide`](./Decide.md) タクティクを使うと良いかもしれません。-/
