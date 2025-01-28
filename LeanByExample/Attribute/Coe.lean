/- # coe

`[coe]` 属性は、特定の関数を[型強制](#{root}/TypeClass/Coe.md)を行う関数として登録し、`↑` 記号で表示されるようにします。-/

/-- 自前で定義した自然数 -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

-- `MyNat.succ` を（意味をなしていないが）型強制として登録する
attribute [coe] MyNat.succ

-- `MyNat.succ` ではなく `↑` と表示されるようになった
/-- info: ↑MyNat.zero : MyNat -/
#guard_msgs in
  #check (MyNat.succ .zero : MyNat)

/- また、`[coe]` 属性は [`norm_cast`](#{root}/Tactic/NormCast.md) タクティクとも関係があります。-/

/- ## 用途
型強制を [`Coe`](#{root}/TypeClass/Coe.md) 型クラスで登録しただけでは、必ずしも型強制を行う関数が `↑` 記号で表示されるわけではありません。`[coe]` 属性を付与することにより、より「型強制らしく」表示されるようになります。
-/

/-- 自然数の組 -/
def IntBase := Nat × Nat

/-- 自然数の組に対する同値関係 -/
def IntBase.equiv : IntBase → IntBase → Prop :=
  fun (a₁, b₁) (a₂, b₂) => a₁ + b₂ = b₁ + a₂

/-- `IntBase` 上の同値関係として `IntBase.equiv` を登録する -/
instance IntBase.setoid : Setoid IntBase where
  r := IntBase.equiv
  iseqv := by
    constructor
    case refl =>
      intro ⟨x, y⟩
      dsimp [IntBase.equiv]
      ac_rfl
    case symm =>
      intro ⟨x, y⟩ ⟨x', y'⟩ h
      dsimp [IntBase.equiv] at *
      omega
    case trans =>
      intro ⟨x, y⟩ ⟨x', y'⟩ ⟨x'', y''⟩ hxy hyz
      dsimp [IntBase.equiv] at *
      omega

/-- 整数を表す型 -/
abbrev myInt := Quotient IntBase.setoid

/-- 自然数を `myInt` に変換する -/
def myInt.ofNat (n : Nat) : myInt := Quotient.mk' (n, 0)

/-- `Nat → myInt` という型強制 -/
instance : Coe Nat myInt where
  coe := myInt.ofNat

-- この時点では、`myInt.ofNat` が型強制として表示されない
/-- info: myInt.ofNat Nat.zero : myInt -/
#guard_msgs in
  #check (Nat.zero : myInt)

-- `[coe]` 属性を付与する
attribute [coe] myInt.ofNat

-- `myInt.ofNat` ではなく `↑` と表示されるようになった！
/-- info: ↑Nat.zero : myInt -/
#guard_msgs in
  #check (Nat.zero : myInt)
