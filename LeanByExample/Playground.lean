/- # 完備束における不動点定理

## 準備: 部分集合の表現
-/

/-- α の部分集合全体 -/
def Set (α : Type) := α → Prop

/-- S : Set α に対して s ∈ S と書けるようにする -/
instance : Membership α (Set α) where
  mem := fun S s => S s

/-
## 束
-/

/-- ⊔ のための記法クラス -/
class Sup (α : Type u) where
  /-- 上限（最小上界） -/
  sup : α → α → α

infixl:65 " ⊔ " => Sup.sup

/-- ⊓ のための記法クラス -/
class Inf (α : Type u) where
  /-- 下限（最大下界） -/
  inf : α → α → α

infixl:70 " ⊓ " => Inf.inf

/-- 束 -/
class IsLattice (α : Type u) [LE α] [Sup α] [Inf α] extends Std.IsPartialOrder α where
  /-- 任意の2元は上限を持つ -/
  sup_le_iff (a b c : α) : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c
  /-- 任意の2元は下限を持つ -/
  le_inf_iff (a b c : α) : c ≤ a ⊓ b ↔ c ≤ a ∧ c ≤ b

grind_pattern IsLattice.sup_le_iff => a ⊔ b, _ ≤ c
grind_pattern IsLattice.le_inf_iff => a ⊓ b, c ≤ _

/-
## 束の基本的性質
-/

variable {L : Type}
variable [LE L] [Sup L] [Inf L]
variable [IsLattice L]

-- 最終的にいるかどうかは不明
theorem Lattice.sup_ub (x y : L) : x ≤ x ⊔ y := by
  grind only [usr IsLattice.sup_le_iff]

/- ## 完備束 -/

class SetSup (α : Type) where
  /-- 集合の上限 -/
  sSup : Set α → α

@[inherit_doc]
prefix:110 "⨆ " => SetSup.sSup

class SetInf (α : Type) where
  /-- 集合の下限 -/
  sInf : Set α → α

@[inherit_doc]
prefix:110 "⨅ " => SetInf.sInf

/-- 完備束 -/
class CompleteLattice (α : Type) [LE α] [Sup α] [Inf α] [SetSup α] [SetInf α] extends IsLattice α where
  /-- 任意の部分集合は上限を持つ -/
  ssup_le_iff (S : Set α) (a : α) : ⨆ S ≤ a ↔ ∀ s ∈ S, s ≤ a
  /-- 任意の部分集合は下限を持つ -/
  le_sinf_iff (S : Set α) (a : α) : a ≤ ⨅ S ↔ ∀ s ∈ S, a ≤ s

/-
## 鎖

> **定義**: 鎖
> 半順序集合 `(P, ≤)` において `C ⊆ P` が鎖(chain)であるとは、`C` の任意の2要素が比較可能であることをいいます。

-/

variable {P : Type} [LE P]

def IsChain (C : Set P) :=
  ∀ x ∈ C, ∀ y ∈ C, x ≤ y ∨ y ≤ x

/-
## 上限
-/

/-- u は S ⊆ P の上界 -/
def IsUpperBound (S : Set P) (u : P) : Prop :=
  ∀ s ∈ S, s ≤ u

/-- u は S ⊆ P の上限 -/
structure IsSup (S : Set P) (u : P) : Prop where
  /-- u は S の上界である -/
  ub : IsUpperBound S u

  /-- u は S の上界の中で最小 -/
  min_ub : ∀ s ∈ S, IsUpperBound S s → u ≤ s
