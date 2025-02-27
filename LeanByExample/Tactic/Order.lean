/- # order

`order` タクティクは、順序関係を扱うための専用のタクティクです。`Preorder` クラスや `PartialOrder`, `LinearOrder` クラスのインスタンスに対して使用することができます。
-/
import Mathlib.Tactic.Order

section
  /- ## Preorder に対して使用する例 -/

  variable {α : Type} [Preorder α] (a b c d : α)

  example (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
    order

  example (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d := by
    order

  example (h1 : a ≤ b) (h2 : ¬ (a < b)) : b ≤ a := by
    order
end

section
  /- ## PartialOrder に対して使用する例 -/

  variable {α : Type} [PartialOrder α] (a b c d : α)

  example (h1 : a ≤ b) (h2 : ¬ (a < b)) : a = b := by
    order

  example : ¬ (a < a) := by
    order
end

section
  /- ## LinearOrder に対して使用する例 -/

  variable {α : Type} [LinearOrder α] (a b c d : α)

  example (h1 : ¬ (a < b)) (h2 : ¬ (b < a)) : a = b := by
    order
end
