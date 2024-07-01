/- # axiom
`axiom` は，公理を宣言するためのコマンドです．公理とは，議論の前提のことで，証明を与えることなく正しいと仮定される命題です．
-/

/-- sorryAx を真似て作った公理 -/
axiom mySorryAx {P : Prop} : P

-- 任意の命題を示すことができる
theorem FLT : ∀ x y z n : Nat, n > 2 → x^n + y^n ≠ z^n := by
  apply mySorryAx

/-- info: 'FLT' depends on axioms: [mySorryAx] -/
#guard_msgs in #print axioms FLT

/- ## 組み込みの公理
組み込みで用意されている公理をいくつか紹介します．

### 命題外延性 `propext`
命題外延性の公理 `propext` は，同値な命題は等しいという公理です．この公理があることにより，どのような状況でも常に命題をそれと同値な命題と置き換えることができます．
-/

-- 命題外延性の公理
/-- info: axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b -/
#guard_msgs in #print propext

-- 命題外延性の公理を使って命題を置換する
theorem ex_prop_ext (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b := by
  have := propext h
  rw [←this]
  assumption

/-- info: 'ex_prop_ext' depends on axioms: [propext] -/
#guard_msgs in #print axioms ex_prop_ext

/- ### 商の公理 `Quot.sound`
任意の型 `α : Sort u` と `α` 上の2項関係 `r : α → α → Prop` に対して，その商(quotient)を作ることができます．商の概念は，以下に示す複数の定数から構成されます．
-/
universe u

variable {α : Sort u}

-- 商
#check (Quot : (α → α → Prop) → Sort u)

-- 商の構築
#check (Quot.mk : (r : α → α → Prop) → α → Quot r)

-- 帰納法の原理.
-- 任意の部分集合 `β ⊆ Quot r` に対して，
-- β が `Quot.mk r a` の形の項を全て含むならば，
-- β は商 `Quot r` 全体に一致する.
#check (Quot.ind :
  {r : α → α → Prop} → {β : Quot r → Prop}
  → (∀ a, β (Quot.mk r a)) → ∀ q, β q)

-- 要するに商 `Quot r` の全ての項は `Quot.mk r a` の形をしている.
-- Quot.ind から直ちに従う.
example (r : α → α → Prop) (q : Quot r) : ∃ a : α, q = Quot.mk r a := by
  have := Quot.ind (β := fun q => ∃ a : α, q = Quot.mk r a)
  apply this
  intro a
  exists a

-- 関数の商へのリフト．
-- 関数 `f : α → β` が，関係 `r` に関して合同性を持つならば，
-- `f` をリフトして関数 `Quot r → β` が得られる.
#check (Quot.lift :
  {r : α → α → Prop} → {β : Sort u} → (f : α → β)
  → (∀ a b, r a b → f a = f b) → Quot r → β)

/- 商の公理 `Quot.sound` は上記の「商のような」概念を本物の商にします．-/

-- `r a b` が成り立つならば，商に送った時に同じ値になることを主張する．
/--
info: axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
r a b → Quot.mk r a = Quot.mk r b
-/
#guard_msgs in #print Quot.sound

/- 商の公理 `Quot.sound` を利用して，関数外延性を示すことができます．関数外延性とは，すべての入力に対して同じ値を返すような２つの関数は等しいという定理です．-/

universe v

variable {β : α → Sort v}

/-- 関数外延性の定理．入力に対して同じ値を返す関数は等しい．-/
theorem my_funext {f g : (x : α) → β x} (h : ∀ x, f x = g x) : f = g := by
  -- 外延性等式を表す二項関係を定義する
  let eqv (f g : (x : α) → β x) := ∀ x, f x = g x

  -- 二項関係 eqv で `(x : α) → β x` の商を取る
  let extfun := Quot eqv

  -- 関数 `f` と `g` は商の定義から，商に送ると等しい！
  have : Quot.mk eqv f = Quot.mk eqv g := Quot.sound (λ x => h x)

  -- 関数適用を行う関数 `(a : α) → ((x : α) → β x) → β a` を考える
  let funApp (a : α) (f : (x : α) → β x) : β a := f a

  -- 関数適用 `funApp` を商 `extfun` 上にリフトする
  let extfunApp (a : α) (f' : extfun) : β a := by
    have lift := @Quot.lift ((x : α) → β x) eqv (β a) (funApp a)
    apply lift
    · intro f g h
      exact h a
    · exact f'

  -- `f = g` を示す問題を `extfunApp` をかませることで，
  -- 商での等式に帰着させることができる.
  calc
    f = fun x => f x := by rfl
    _ = extfunApp (f' := Quot.mk eqv f) := by rfl
    _ = extfunApp (f' := Quot.mk eqv g) := by rw [this]
    _ = fun x => g x := by rfl
    _ = g := by rfl

/-- info: 'my_funext' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms my_funext

/- ## 選択原理 `Classical.choice`
選択原理は，Lean 版選択公理とでも言うべきものです．選択原理は，ある型が空ではないという情報だけから，「魔法のように」具体的な元を構成することができると主張します．
-/

-- Nonempty は，型が単に空ではないことを表す
/--
info: inductive Nonempty.{u} : Sort u → Prop
number of parameters: 1
constructors:
Nonempty.intro : ∀ {α : Sort u}, α → Nonempty α
-/
#guard_msgs in #print Nonempty

-- 選択原理は，空でない型から具体的な元を構成する
/-- info: axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α -/
#guard_msgs in #print Classical.choice
