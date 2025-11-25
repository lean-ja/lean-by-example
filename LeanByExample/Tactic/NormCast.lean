/- # norm_cast

`norm_cast` は、型キャスト（ある型からある型への変換）を簡約するタクティクです。

詳細については論文 [「Simplifying Casts and Coercions」](https://arxiv.org/abs/2001.10594) などを参照してください。
-/
import Mathlib.Tactic

-- `x, m, n` は自然数とする
variable (x m n : ℕ)

example (left : (x : ℝ) < ↑m + ↑n) (right : ↑m + ↑n < (x : ℝ) + 1) : False := by
  -- `linarith` では示すことができない
  fail_if_success linarith

  -- `omega` でも示すことができない
  fail_if_success omega

  -- 仮定の `left` と `right` は実数上の不等式だが、
  -- 自然数上の不等式と解釈できるはずである。
  -- `norm_cast` はそれを実行してくれる。
  norm_cast at left right

  -- 仮定が自然数における不等式に変わった！
  guard_hyp left : x < m + n
  guard_hyp right : m + n < x + 1

  -- 後は `omega` で示せる
  omega

/- ## [norm_cast] 属性によるカスタマイズ

命題に `[norm_cast]` 属性を付与することにより、`norm_cast` タクティクでできることを増やすことができます。
-/

/-- 自然数のペア -/
def IntBase := Nat × Nat

/-- 自然数のペアが「整数として等しい」という同値関係 -/
def IntBase.equiv : IntBase → IntBase → Prop :=
  fun (a₁, b₁) (a₂, b₂) => a₁ + b₂ = b₁ + a₂

/-- `IntBase` と同値関係 `IntBase.equiv` をペアにする -/
@[instance] def IntBase.sequiv : Setoid IntBase where
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

/-- 自前で定義した整数 -/
abbrev MyInt := Quotient IntBase.sequiv

/-- 自然数を `myInt` と解釈する関数 -/
def MyInt.ofNat (n : Nat) : MyInt := ⟦(n, 0)⟧

@[grind →]
theorem MyInt.ofNat_inj (n m : Nat) : MyInt.ofNat n = MyInt.ofNat m → n = m := by
  intro h
  dsimp [MyInt.ofNat] at h
  have h' : IntBase.equiv (n, 0) (m, 0) := by
    apply Quotient.exact h
  suffices IntBase.equiv (n, 0) (m, 0) from by
    grind [= IntBase.equiv]
  assumption

/-- 型強制を定義 -/
instance : Coe Nat MyInt where
  coe := MyInt.ofNat

/-- 型キャストの簡約を行う補題。`ℕ` の項が `myInt` として等しいなら、元から等しい。 -/
theorem MyInt_eq {x y : ℕ} : (x : MyInt) = (y : MyInt) ↔ x = y := by
  constructor <;> intro h
  · grind
  · rw [h]

-- `[norm_cast]` 属性の制約として、
-- 登録する補題の中には型強制が含まれていなくてはいけない
-- たとえば `↑` など
/-⋆-//--
error: Invalid `norm_cast` lemma: At least one coe function must appear in the left-hand side
  MyInt.ofNat x = MyInt.ofNat y

Note: coe functions are registered using the `[coe]` attribute
-/
#guard_msgs in --#
attribute [norm_cast] MyInt_eq

-- `[coe]` 属性を付与し、`MyInt.ofNat` を型キャストを行う関数として認識させる
attribute [coe] MyInt.ofNat

set_option linter.unusedTactic false in --#
example {x y z : ℕ} (h : (x : MyInt) = (y : MyInt)) : x + z = y + z := by
  norm_cast at h

  -- `norm_cast` の効果が出ていない
  guard_hyp h : (x : MyInt) = (y : MyInt)
  simp [MyInt_eq] at h
  omega

-- `norm_cast` に使ってもらえるように登録する
attribute [norm_cast] MyInt_eq

example {x y z : Nat} (h : (x : MyInt) = (y : MyInt)) : x + z = y + z := by
  norm_cast at h

  -- `norm_cast` で簡約できるようになった！
  guard_hyp h : x = y

  omega
