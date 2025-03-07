/- # Setoid

`Setoid` は、与えられた型の上の同値関係を表します。具体的には、`α : Type` に対してインスタンス `sa : Setoid α` は、`α` 上の二項関係 `r : α → α → Prop` と `r` が同値関係であることの証明の組です。

`Setoid` は、次のように定義されています。
-/
--#--
-- ## Setoidの定義の確認
/--
info: class Setoid.{u} (α : Sort u) : Sort (max 1 u)
number of parameters: 1
fields:
  Setoid.r : α → α → Prop
  Setoid.iseqv : Equivalence Setoid.r
constructor:
  Setoid.mk.{u} {α : Sort u} (r : α → α → Prop) (iseqv : Equivalence r) : Setoid α
-/
#guard_msgs in #print Setoid
--#--
namespace Hidden --#

/--
Setoidは、特定の同値関係（`≈`で表される）を持つ。
これは主に`Quotient`型への入力として使用される。
-/
class Setoid.{u} (α : Sort u) where
  /-- `α` 上の二項関係 -/
  r : α → α → Prop
  /-- `r` は同値関係 -/
  iseqv : Equivalence r

end Hidden --#
/- ## 使用例

たとえば、ある型 `α` 上の関数 `f : α → β` が与えられていて `β` 上に同値関係 `(· ≈ ·)` が定義されているとします。このとき `α` 上の二項関係 `r` を `r a b := f a ≈ f b` と定義すると、`r` は同値関係になります。

証明してみましょう。
-/
section
  variable {α : Type} {β : Type}

  /-- `β` 上の二項関係から誘導される `α` 上の二項関係 -/
  def Rel.contra_map (f : α → β) (r : β → β → Prop) : α → α → Prop :=
    fun a₁ a₂ => r (f a₁) (f a₂)

  /-- `β` 上の同値関係から誘導される `α` 上の同値関係 -/
  def Setoid.contra_map [Setoid β] (f : α → β) : Setoid α where
    r := Rel.contra_map f (· ≈ ·)
    iseqv := by
      constructor <;> dsimp [Rel.contra_map]

      -- 反射律
      case refl =>
        intro x
        apply Setoid.iseqv.refl

      -- 対称律
      case symm =>
        intro x y
        apply Setoid.iseqv.symm

      -- 推移律
      case trans =>
        intro x y z
        apply Setoid.iseqv.trans
end
