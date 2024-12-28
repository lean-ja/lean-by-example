/- # ring

`ring` は、可換環(commutative ring)の等式を示します。ローカルコンテキストの仮定は読まず、環の公理だけを使います。-/
import Mathlib.Tactic.Ring -- `ring` のために必要
import Mathlib.Tactic.Says --#

example (x y : ℤ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

example (x y z : ℤ) (hz : z = x + y) : x * z = x ^ 2 + x * y := by
  -- `ring` はローカルコンテキストの仮定を読まないので、証明できない
  fail_if_success solve
  | ring

  -- `rw` などで、環の公理だけを使って示せる形にすれば証明できるようになる
  rw [hz]
  ring

/- ## ring_nf
`ring` は等式を示そうとするタクティクですが、`ring_nf` は式を整理して標準形と呼ばれる形にします。`ring` とは異なり、部分項の変形まで行うことができます。
-/
example {x y : Rat} (F : Rat → Rat) : F (x + y) + F (y + x) = 2 * F (x + y) := by
  ring_nf

/- ## 環でないものに対する振る舞い

たとえば自然数 `Nat` はマイナスがないので環ではありません。そのため、自然数の引き算などを含む式は多くの場合 `ring` では示せません。代わりに `ring_nf` を使うように促されますが、`ring_nf` でも示せるとは限りません。
-/

-- Lean では自然数の引き算は
-- `n ≤ m` のとき `n - m = 0` になるように定義されている
example : 7 - 42 = 0 := rfl

-- 整数にすると結果が変わる
example : 7 - (42 : ℤ) = - 35 := rfl

example {n : Nat} : n - n + n = n := by
  -- `ring_nf` を提案される
  ring says ring_nf

  simp

example {n : Nat} : n - n + n = n := by
  -- 提案通りに `ring_nf` を使っても証明できない
  fail_if_success solve
  | ring_nf

  -- ゴールが変わっていない
  guard_target =ₛ n - n + n = n

  simp

/- 自然数 `Nat` は半環(semiring)ですが、`ring` は可換な半環に対しても使用することができるので自然数の和と積についての式は `ring` で示すことができます。-/

example (n m : Nat) : (n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2 := by
  ring

example (n m : Nat) : n * (n + m) = n ^ 2 + n * m := by
  ring

/- ## カスタマイズ

新たに型 `R : Type` に対して `ring` タクティクが利用できるようにするためには、`R` を `CommSemiring` または `CommRing` のインスタンスにします。
-/

/-- 組み込みの自然数のラッパー -/
@[ext] structure MyNat : Type where
  val : Nat

/-- `MyNat` に掛け算を定義 -/
instance : Mul MyNat where
  mul x y := ⟨x.val * y.val⟩

/-- `MyNat` に足し算を定義 -/
instance : Add MyNat where
  add x y := ⟨x.val + y.val⟩

/-- `MyNat` として等しいことと、`val` を取って自然数として等しいことは同値 -/
@[simp]
theorem MyNat.translate (m n : MyNat) : m = n ↔ m.val = n.val := by
  constructor <;> intro h
  · rw [h]
  · ext
    assumption

/-- `MyNat` の和を自然数の和に翻訳する -/
@[simp] theorem MyNat.add_val (m n : MyNat) : (m + n).val = m.val + n.val := by rfl

/-- `MyNat` の積を自然数の積に翻訳する -/
@[simp] theorem MyNat.mul_val (m n : MyNat) : (m * n).val = m.val * n.val := by rfl

example (m n : MyNat) : n * (n + m) = n * n + n * m := by
  -- `ring` は `MyNat` に対しては使えない
  fail_if_success solve
  | ring

  -- 自然数の話に翻訳して示す
  suffices goal : n.val * (n.val + m.val) = n.val * n.val + n.val * m.val from by
    simpa
  ring

/-- `MyNat` についての等式を自然数に翻訳して示す -/
local macro "translate" : tactic => `(tactic| with_reducible
  intros
  simp
  try ring
)

/-- `MyNat` は加法について半群(semigroup)である -/
instance : AddSemigroup MyNat where
  add_assoc := by translate

instance : Zero MyNat where
  zero := ⟨0⟩

/-- `MyNat` のゼロを自然数のゼロに翻訳する -/
@[simp] theorem MyNat.zero_val : (0 : MyNat).val = 0 := by rfl

/-- `MyNat` は加法についてモノイドである -/
instance : AddMonoid MyNat where
  zero_add := by translate
  add_zero := by translate
  nsmul := fun n a => ⟨n * a.val⟩
  nsmul_zero := by translate
  nsmul_succ := by translate

instance : One MyNat where
  one := ⟨1⟩

/-- `MyNat` の1を自然数の1に翻訳する -/
@[simp] theorem MyNat.one_val : (1 : MyNat).val = 1 := by rfl

/-- `MyNat` は可換な半環(semiring)である -/
instance : CommSemiring MyNat where
  add_comm := by translate
  left_distrib := by translate
  right_distrib := by translate
  zero_mul := by translate
  mul_zero := by translate
  mul_assoc := by translate
  one_mul := by translate
  mul_one := by translate
  mul_comm := by translate

example (m n : MyNat) : n * (n + m) = n * n + n * m := by
  -- `ring` が使えるようになった！
  ring
