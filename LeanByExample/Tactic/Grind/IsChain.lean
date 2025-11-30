/-- 二項関係`R`がリストの隣接要素に対して成立するという述語。
つまり `[x₁, x₂, ..., xₙ].IsChain R` は `R x₁ x₂ ∧ R x₂ x₃ ∧ ... ∧ R xₙ₋₁ xₙ` を表す。-/
inductive List.IsChain {α : Type} (R : α → α → Prop) : List α → Prop
  | nil : IsChain R []
  | single (a : α) : IsChain R [a]
  | cons_cons {a b : α} {l : List α} (hab : R a b) (ih : IsChain R (b :: l)) :
    IsChain R (a :: b :: l)

namespace List

variable {α : Type} {R : α → α → Prop}

-- `grind`を使用しない証明の例
example (a b : α) (h : R a b) : [a, b].IsChain R := by
  apply IsChain.cons_cons h
  apply IsChain.single

-- `grind_pattern`を使って定理のインスタンス化を`grind`に指示する。
-- ローカルコンテキストに`=>`の右側のパターンを見かけたらインスタンス化させる。
grind_pattern IsChain.cons_cons => IsChain R (a :: b :: l)
grind_pattern IsChain.single => IsChain R [a]

example (a b : α) (h : R a b) : [a, b].IsChain R := by
  -- 一撃で片づけることができるようになった
  grind

end List
