/- # Quotient

`Quotient` は、型 `α` 上の同値関係 `r : Setoid α` による **商(quotient)** を表します。[`Setoid`](#{root}/TypeClass/Setoid.md) を受け取って、商型を返します。

-/

/-- 自然数を２つペアにしたもの -/
abbrev PreInt := Nat × Nat

namespace MyPreInt
  /- ## MyIntのための同値関係の構成 -/

  def rel (m n : PreInt) : Prop :=
    match m, n with
    | (m₁, m₂), (n₁, n₂) => m₁ + n₂ = m₂ + n₁

  /-- 反射律 -/
  theorem rel.refl : ∀ (m : PreInt), rel m m := by
    intro (m₁, m₂)
    dsimp [rel]
    ac_rfl

  /-- 対称律 -/
  theorem rel.symm : ∀ {m n : PreInt}, rel m n → rel n m := by
    intro (m₁, m₂) (n₁, n₂) h
    dsimp [rel] at *
    omega

  /-- 推移律 -/
  theorem rel.trans : ∀ {l m n : PreInt}, rel l m → rel m n → rel l n := by
    intro (l₁, l₂) (m₁, m₂) (n₁, n₂) hlm hmn
    dsimp [rel] at *
    omega

  /-- `MyPreInt.rel`は同値関係 -/
  theorem rel.equiv : Equivalence rel :=
    { refl := rel.refl, symm := rel.symm, trans := rel.trans }

  /-- `MyPreInt`に同値関係を紐づける -/
  instance r : Setoid PreInt := ⟨rel, rel.equiv⟩

end MyPreInt

/-- 整数の定義 -/
def MyInt := Quotient MyPreInt.r
