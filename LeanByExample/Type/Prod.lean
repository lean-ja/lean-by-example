import Mathlib.Logic.Equiv.Defs --#
/- # Prod

`Prod` は、データを重ね合わせたものを表現しており、`Prod A B` は `A` のデータと `B` のデータの両方を持たされているようなデータの集まりです。`A × B` と表記されます。
-/

example {A B : Type} : Prod A B = (A × B) := by rfl

#check (Prod.mk 3 "hello" : Nat × String)

/- `(x₁, x₂, .., xₙ)` という構文で項を表すことができます。 -/

#guard (3, "hello") = Prod.mk 3 "hello"

/- ## カリー化

`A × B → C` と `A → B → C` の間に自然な全単射が存在し、同値になることが知られています。
-/

example {A B C : Type} : (A × B → C) ≃ (A → B → C) where
  toFun f a b := f (a, b)
  invFun f p := f p.1 p.2
  left_inv := by
    intro f
    funext p
    cases p
    rfl
  right_inv := by
    intro f
    funext a b
    rfl

/- この同値関係を使って `A × B` 上の関数をばらして定義域から積を消す操作を **カリー化** と呼びます。カリー化を行うと部分適用を行いやすくなるので、Lean では関数は常にカリー化することが推奨されます。 -/
