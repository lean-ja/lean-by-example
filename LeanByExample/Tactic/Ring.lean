/- # ring

`ring` は、可換環(commutative ring)上の等式を示すタクティクです。[「Proving Equalities in a Commutative Ring Done Right in Coq」](https://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf) という論文に基づいて実装されています。

ただし環とは、加法 `+` と乗法 `*` とマイナスを取る演算 `-` が定義されていて、それぞれが分配法則や結合法則などのいくつかの法則を満たしているものをいいます。その中でも乗法が可換、つまり `a * b = b * a` が成り立つような環を可換環と呼びます。可換環の典型的な例は、整数全体 `ℤ` や有理数全体 `ℚ` や、多項式環 `ℚ[X]` などです。
-/
import Mathlib.Tactic.Ring -- `ring` のために必要
import Mathlib.Tactic.Says --#

example (x y : ℤ) : (x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2 := by
  ring

example (x : ℤ) : x ^ 3 - 1 = (x ^ 2 + x + 1) * (x - 1) := by
  ring

/- また、可換な半環(semiring)上の等式も示すことができます。

ただし半環とは、加法 `+` と乗法 `*` が定義されていて、分配法則や結合法則などの法則が満たされているものをいいます。半環の典型的な例は、自然数全体 `ℕ` などです。
-/

example (n m : Nat) : (n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2 := by
  ring

example (n m : Nat) : (n + m) ^ 3 = n ^ 3 + 3 * n * m * (n + m) + m ^ 3 := by
  ring

/- `ring` はローカルコンテキストの仮定は読まず、(半)環の公理だけを使います。 -/

example (x y z : ℤ) (hz : z = x - y) : x * z = x ^ 2 - x * y := by
  -- `ring` はローカルコンテキストの仮定を読まないので、証明できない
  fail_if_success solve
  | ring

  -- `rw` などで、環の公理だけを使って示せる形にすれば証明できるようになる
  rw [hz]
  ring

/- ## ring_nf

自然数 `ℕ` は可換環にならないので、自然数の引き算に関する式を証明しようとすると上手くいきません。[`ring_nf`](./RingNf.md) タクティクを提案されますが、`ring_nf` に変更すれば成功するとは限りません。
-/

example {n : Nat} : n - n + n = n := by
  -- `ring_nf` を提案される
  ring says ring_nf

  simp

example {n : Nat} : n - n + n = n := by
  -- 提案通りに `ring_nf` を使っても証明できない
  fail_if_success solve
  | ring_nf

  simp

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
