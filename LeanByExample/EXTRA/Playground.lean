/- # 完備束における不動点定理

## 準備: 部分集合の表現
-/

/-- α の部分集合全体 -/
def Set (α : Type) := α → Prop

/-- S : Set α に対して s ∈ S と書けるようにする -/
instance : Membership α (Set α) where
  mem := fun S s => S s

/-- 述語から、それが内包によって定める部分集合を作る -/
def setOf (P : X → Prop) : Set X := P

/-- binder という構文カテゴリ。
これは変数束縛を表していて、
`{x : X | P x}` の `x : X` の部分とか
`{x ∈ X | P x}` の `x ∈ X` の部分とかを表している -/
declare_syntax_cat binder

/-- `{x : T | P x}` の `: T` の部分。
あってもなくても良いので `( )?` で囲う -/
syntax ident (" : " term)? : binder

/-- `{x ∈ T | P x}` の `∈ T` の部分。
あってもなくても良いので `( )?` で囲う -/
syntax ident (" ∈ " term)? : binder

/-- 集合の内包表記 -/
syntax "{" binder "|" term "}" : term

/-- `{x : T | P x}` と `{x ∈ T | P x}` の形の式を `setOf` の式に変換する -/
macro_rules
  | `({ $var:ident | $body:term }) => `(setOf (fun $var => $body))
  | `({ $var:ident : $ty:term | $body:term }) => `(setOf (fun ($var : $ty) => $body))
  | `({ $var:ident ∈ $s:term | $body:term }) => `(setOf (fun $var => $var ∈ $s ∧ $body))

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

variable (α : Type) [LE α] [Sup α] [Inf α]

/-- 束 -/
class IsLattice extends Std.IsPartialOrder α where
  /-- 任意の2元は上限を持つ -/
  sup_le_iff (a b c : α) : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c
  /-- 任意の2元は下限を持つ -/
  le_inf_iff (a b c : α) : c ≤ a ⊓ b ↔ c ≤ a ∧ c ≤ b

grind_pattern IsLattice.sup_le_iff => a ⊔ b, _ ≤ c
grind_pattern IsLattice.le_inf_iff => a ⊓ b, c ≤ _

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

variable [SetSup α] [SetInf α]

/-- 完備束 -/
class CompleteLattice extends IsLattice α where
  /-- 任意の部分集合は上限を持つ -/
  ssup_le_iff (S : Set α) (a : α) : ⨆ S ≤ a ↔ ∀ s ∈ S, s ≤ a
  /-- 任意の部分集合は下限を持つ -/
  le_sinf_iff (S : Set α) (a : α) : a ≤ ⨅ S ↔ ∀ s ∈ S, a ≤ s

grind_pattern CompleteLattice.ssup_le_iff => ⨆ S, _ ≤ a
grind_pattern CompleteLattice.le_sinf_iff => ⨅ S, a ≤ _

/-
## 完備束上の不動点定理
-/

-- 以下 α は完備束とする
variable [CompleteLattice α]

theorem CompleteLattice.fixpoint (f : α → α) (hmono : ∀ a b : α, a ≤ b → f a ≤ f b) :
    ∃ u : α, f u = u := by
  -- x ≤ f x を満たす元全体の上限を、不動点の候補とする。
  let S := { x : α | x ≤ f x }
  let u : α := ⨆ S

  -- 定義より u は S の上界である。
  have u_upper : ∀ x ∈ S, x ≤ u := by
    grind

  -- 任意の x ∈ S に対して x ≤ f x ≤ f u なので、u ≤ f u となる。
  have hu : u ≤ f u := by
    suffices ∀ x ∈ S, x ≤ f u from by
      grind
    intro x (hx : x ∈ S)
    calc
      x ≤ f x := hx
      _ ≤ f u := by grind only -- f の単調性を使用

  -- 単調性により f u ≤ f (f u)、すなわち f u ∈ S が成り立つ。
  have hfu : f u ∈ S := hmono u (f u) hu

  -- u は S の上界なので、逆向きの不等式 f u ≤ u も得られる。
  have hfu_le : f u ≤ u := u_upper (f u) hfu

  -- 両方向の不等号が得られたので f u = u。
  exact ⟨u, by grind only⟩
