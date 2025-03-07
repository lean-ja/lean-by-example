/- # Quotient

`Quotient` は、型 `α` 上の同値関係 `r : Setoid α` による **商(quotient)** を表します。[`Setoid`](#{root}/TypeClass/Setoid.md) を受け取って、商型を返します。商とは、ある二項関係 `r : α → α → Prop` によって同じと見なされるものを同一視したものです。

## 具体例: 人間の性別による商

たとえば人間全体の集まり `Human : Type` において `gender : Human → Gender` を性別を返す関数とし、`gender` は正しく定義されているものとします。
-/

/-- 人間たちの集まり -/
opaque Human : Type

/-- 性別 -/
inductive Gender where
  /-- 男性 -/
  | male
  /-- 女性 -/
  | female
deriving Inhabited, DecidableEq

/-- ある人の性別を取得する関数 -/
opaque gender : Human → Gender

/- このとき二項関係 `r : Human → Human → Prop` を `r a b := gender a = gender b` と定義すると、`r` は同値関係になり、`sr : Setoid Human` が得られます。-/

/-- 性別が同じという二項関係 -/
def Human.r (a b : Human) : Prop := gender a = gender b

/-- 性別が同じという同値関係 -/
@[instance] def Human.sr : Setoid Human := ⟨Human.r, by
  constructor
  case refl =>
    intros
    rfl
  case symm =>
    intro x y rxy
    exact rxy.symm
  case trans =>
    intro x y z rxy ryz
    dsimp [Human.r] at *
    have : gender x = gender z := calc
      _ = gender y := rxy
      _ = gender z := ryz
    assumption
  ⟩

/- `sr : Setoid Human` による `Human` の商 `Quotient sr` を考えます。すると、`sr` の定義の言い換えとして、`gender : Human → Gender` は同値関係 `sr` (`Setoid` なので `(· ≈ ·)` と表すことができる)を保ちます。つまり `x ≈ y → gender x = gender y` です。したがって、関数 `Quotient sr → Gender` が誘導されます。 -/

/-- Human の Human.sr による商 -/
def «Human/≈» := Quotient Human.sr

@[simp]
theorem Human.sr_def (a b : Human) : a ≈ b ↔ gender a = gender b := by
  rfl

/-- 商集合から性別への関数 -/
def «↑gender» : «Human/≈» → Gender := Quotient.lift gender <| by
  intro a b rab
  simp_all

/- ここで、仮定として「男性も女性も少なくとも1人構成的に存在する」ことを追加します。これは、関数 `Gender → Human` が存在することとして表現できます。このとき、自然な関数 `Human → «Human/≈»` と合成することによって `Gender → «Human/≈»` という関数が得られます。-/

/-- 男性も女性も少なくとも1人存在し、具体的に指摘することができる -/
axiom pick : Gender → Human

/-- `pick` 関数の仕様 -/
axiom Human.gender_pick_eq_id (g : Gender) : gender (pick g) = g

noncomputable def «pick↑» : Gender → «Human/≈» := fun g =>
  Quotient.mk Human.sr <| pick g

/- このとき、`↑gender` と `pick↑` は互いに逆の関係にあります。つまり、`↑gender ∘ pick↑ = id` であり `pick↑ ∘ ↑gender = id` が成り立ちます。つまり、`Human/≈` と `Gender` は型として同値です。 -/

theorem Human.gender_pick_eq_id' (g : Gender) : «↑gender» («pick↑» g) = g := calc
  _ = gender (pick g) := rfl -- 定義から従う
  _ = g := by apply Human.gender_pick_eq_id

theorem Human.pick_gender_eq_id' (a : «Human/≈») : «pick↑» («↑gender» a) = a := by
  -- `a : Human/≈` が与えられているが、
  -- `a = Quotient.mk Human.sr ax` を満たす `ax : Human` が存在する
  induction a using Quotient.inductionOn with
  | h ax =>
    -- 商の公理により、「商に送って等しい」ことは「元の型上で同値であること」から従う
    dsimp [«pick↑»]
    apply Quotient.sound

    -- 同値関係を定義にばらす
    dsimp [(· ≈ ·), Setoid.r, Human.r]

    have : gender (pick («↑gender» (Quotient.mk sr ax))) = gender ax := calc
      _ = gender (pick (gender ax)) := rfl -- 定義から従う
      _ = gender ax := by rw [Human.gender_pick_eq_id]
    assumption

/- ## 具体例：自然数の積の商として整数を得る -/

/-- 自然数を２つペアにしたもの -/
abbrev PreInt := Nat × Nat

namespace MyPreInt
  /- ## MyIntのための同値関係の構成 -/

  /-- PreInt 上の二項関係 -/
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

  /-- `PreInt.rel`は同値関係 -/
  theorem rel.equiv : Equivalence rel :=
    { refl := rel.refl, symm := rel.symm, trans := rel.trans }

  /-- `PreInt` 上の同値関係 -/
  @[instance] def srel : Setoid PreInt := ⟨rel, rel.equiv⟩

end MyPreInt

/-- 整数の定義 -/
def MyInt := Quotient MyPreInt.srel
