/- # 2.2 順序集合, p.12 から -/

namespace TAPL

/- ## 定義 2.2.1 -/
section

-- 集合Sとその上の二項関係Rを考えたい
variable {S : Type} (R : S → S → Prop)

local infix:50 "∼R" => R

/-- 二項関係が反射的 -/
def Reflexive := ∀ x, x ∼R x

/-- 二項関係が対称的 -/
def Symmetric := ∀ x y, x ∼R y → y ∼R x

/-- 二項関係が推移的 -/
def Transitive := ∀ x y z, x ∼R y → y ∼R z → x ∼R z

/-- 二項関係が反対称的 -/
def Antisymmetric := ∀ x y, x ∼R y → y ∼R x → x = y

end

/- ## 定義 2.2.2 -/

/-- 前順序集合 -/
class Preorder (α : Type) [LE α] [LT α] where
  refl : @Reflexive α (· ≤ ·) -- **TODO** 暗黙引数の明示化が必要になる例では？
  trans : @Transitive α (· ≤ ·)
  /-- `a < b`のデフォルト実装 -/
  lt_def := fun (a b : α) => a < b ↔ a ≤ b ∧ a ≠ b

/-- 半順序集合 -/
class PartialOrder (α : Type) [LE α] [LT α] extends Preorder α where
  antisymm : @Antisymmetric α (· ≤ ·)

/-- 全順序集合 -/
class LinearOrder (α : Type) [LE α] [LT α] extends PartialOrder α where
  total : ∀ a b : α, a ≤ b ∨ b ≤ a


/- ## 定義 2.2.3 -/
section

variable {S : Type} [LE S] [LT S] [PartialOrder S] (s t : S)

/-- `j`は`s`と`t`の結び(join)、または上限 -/
def Join (j : S) := s ≤ j ∧ t ≤ j ∧ (∀ k : S, s ≤ k ∧ t ≤ k → j ≤ k)

/-- `j`は`s`と`t`の交わり(meet)、または下限 -/
def Meet (m : S) := m ≤ s ∧ m ≤ t ∧ (∀ n : S, n ≤ s ∧ n ≤ t → n ≤ m)

end


/- ## 定義 2.2.4 -/

/-- 同値関係 -/
def Equivalence {α : Type} (R : α → α → Prop) :=
  Reflexive R ∧ Symmetric R ∧ Transitive R


/- ## 定義 2.2.5 -/
section

variable {S : Type}

/-- 反射的閉包 -/
inductive ReflClosure (R : S → S → Prop) : S → S → Prop where
  | incl : ∀ x y, R x y → ReflClosure R x y
  | refl : ∀ x, ReflClosure R x x

/-- 推移的閉包 -/
inductive TransClosure (R : S → S → Prop) : S → S → Prop where
  | incl : ∀ x y, R x y → TransClosure R x y
  | trans : ∀ x y z, TransClosure R x y → TransClosure R y z → TransClosure R x z

@[inherit_doc TransClosure] postfix:max "⁺" => TransClosure

/-- 反射的推移的閉包 -/
@[grind]
inductive ReflTransClosure (R : S → S → Prop) : S → S → Prop where
  | incl : ∀ x y, R x y → ReflTransClosure R x y
  | refl : ∀ x, ReflTransClosure R x x
  | trans : ∀ x y z, ReflTransClosure R x y → ReflTransClosure R y z → ReflTransClosure R x z

@[inherit_doc ReflTransClosure] postfix:max "⋆" => ReflTransClosure

end

/- ## 演習 2.2.6 -/
section

variable {S : Type} (R : S → S → Prop)

/-- `Prime R := R ∪ {(s, s) ∣ s ∈ S}` -/
def Prime := fun x y => R x y ∨ x = y

example : ReflClosure R = Prime R := by
  grind [Prime, ReflClosure] -- `grind`を使用すると練習にならない

-- `grind`や`simp_all`などの自動化ツールを使わずに証明した場合
example : ReflClosure R = Prime R := by
  ext x y
  constructor <;> intro h
  case mp =>
    dsimp [Prime]
    cases h with
    | @incl S hr =>
      left
      assumption
    | refl =>
      right
      rfl
  case mpr =>
    dsimp [Prime] at h
    cases h with
    | inl h =>
      apply ReflClosure.incl
      assumption
    | inr h =>
      rw [h]
      apply ReflClosure.refl

end

/- ## 演習 2.2.7 -/
section

variable {S : Type} (R : S → S → Prop)

/-- 構成的推移的閉包 -/
def CTC (n : Nat) : S → S → Prop :=
  match n with
  | 0 => R
  | i + 1 =>
    fun x y => CTC i x y ∨ (∃ t, CTC i x t ∧ CTC i t y)

def Plus : S → S → Prop := fun x y => ∃ n, CTC R n x y

/-- ある`n`について`CTC R n`が成り立つなら、推移的閉包も成り立つ -/
theorem TransClosure_of_CTC (n : Nat) (x y : S) : (CTC R n) x y → TransClosure R x y := by
  induction n generalizing x y
  all_goals
    dsimp [CTC]
    grind [TransClosure]

/-- `CTC`は`n`が大きくなるほど成り立つ要素が多くなる -/
theorem CTC_of_le {x y : S} {n m : Nat} (h : n ≤ m) : (CTC R n) x y → (CTC R m) x y := by
  induction h with grind [CTC]

/-- `Plus R`は`R`の推移的閉包である -/
example : Plus R = TransClosure R := by
  ext x y
  dsimp [Plus]
  constructor <;> intro h
  case mp => grind [TransClosure_of_CTC]
  case mpr =>
    dsimp [Plus]
    induction h with
    | incl s t hr =>
      exists 0
    | trans x' y' z' ixy iyz cxy cyz =>
      obtain ⟨n, cxy⟩ := cxy
      obtain ⟨m, cyz⟩ := cyz
      exists n + m + 1
      replace cxy := CTC_of_le R (show n ≤ n + m from by omega) cxy
      replace cyz := CTC_of_le R (show m ≤ n + m from by omega) cyz
      grind only [CTC]

end

/- ## 演習2.2.8 -/
section

variable {S : Type} (R : S → S → Prop) (P : S → Prop)

/-- 二項関係`R`が述語`P`を保つ -/
@[grind]
def BinRel.preserve (R : S → S → Prop) (P : S → Prop) :=
  ∀ x y, R x y → P x → P y

-- **TODO** 非自明(そうに見えて)かつおもしろい例なので、帰納的述語に慣れるのにいい例だと思う。
/-- 二項関係`R`が述語`P`を保つなら、その反射的推移的閉包も述語`P`を保つ。 -/
example (hr : BinRel.preserve R P) : BinRel.preserve R⋆ P := by
  intro s s' h hps
  induction h with grind

-- `grind`を使わずに証明した場合
example (hr : BinRel.preserve R P) : BinRel.preserve R⋆ P := by
  intro s s' h hps
  induction h with
  | incl x y h =>
    exact hr x y h hps
  | refl x => assumption
  | trans x y z hxy hyz ihxy ihyz =>
    apply ihyz
    apply ihxy
    assumption

end
end TAPL
