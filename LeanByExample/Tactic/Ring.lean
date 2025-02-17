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

`ring` が扱える対象には制約があり、たとえば自然数 `ℕ` は可換環にならないので、自然数の引き算に関する等式を証明しようとしても上手くいきません。[`ring_nf`](./RingNf.md) タクティクを提案されますが、`ring_nf` に変更すれば成功するとは限りません。
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

/- 実際、`ring` タクティクは失敗すると常に `ring_nf` を提案するようなマクロとして定義されています。 -/
section
  open Lean

  /-- `#expand` の入力に渡すための構文カテゴリ -/
  syntax macro_stx := command <|> tactic <|> term

  /-- マクロを展開するコマンド -/
  elab "#expand " "(" stx:macro_stx ")" : command => do
    let t : Syntax :=
      match stx.raw with
      | .node _ _ #[t] => t
      | _ => stx.raw
    match ← Elab.liftMacroM <| Macro.expandMacro? t with
    | none => logInfo m!"Not a macro"
    | some t => logInfo m!"{t}"
end

-- マクロ展開の中に `try_this ring_nf` が含まれる
/--
info: first
| ring1
|
  try_this ring_nf"\n\nThe `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
      \nNote that `ring` works primarily in *commutative* rings. \
      If you have a noncommutative ring, abelian group or module, consider using \
      `noncomm_ring`, `abel` or `module` instead."
-/
#guard_msgs (info, drop warning) in
  #expand (ring)

/- ## カスタマイズ

新たに型 `R : Type` に対して `ring` タクティクが利用できるようにするためには、`R` を `CommSemiring` または `CommRing` のインスタンスにします。
-/

/-- 組み込みの自然数のラッパー -/
@[ext] structure MyNat : Type where
  val : Nat

namespace MyNat
  /- ## MyNat に掛け算と足し算を定義する -/

  /-- `MyNat` に掛け算を定義 -/
  instance : Mul MyNat where
    mul x y := ⟨x.val * y.val⟩

  /-- `MyNat` に足し算を定義 -/
  instance : Add MyNat where
    add x y := ⟨x.val + y.val⟩

end MyNat

#guard_msgs (drop warning) in --#
example (m n : MyNat) : n * (n + m) = n * n + n * m := by
  -- `ring` は `MyNat` に対しては使えない
  fail_if_success solve
  | ring

  sorry

namespace MyNat
  /- ## MyNat が半環であることを証明するための準備 -/

  /-- `MyNat` として等しいことと、`val` を取って自然数として等しいことは同値 -/
  @[simp]
  theorem translate (m n : MyNat) : m = n ↔ m.val = n.val := by
    constructor <;> intro h
    · rw [h]
    · ext
      assumption

  /-- `MyNat` の和を自然数の和に翻訳する -/
  @[simp] theorem add_val (m n : MyNat) : (m + n).val = m.val + n.val := by rfl

  /-- `MyNat` の積を自然数の積に翻訳する -/
  @[simp] theorem mul_val (m n : MyNat) : (m * n).val = m.val * n.val := by rfl

  /-- `MyNat` についての等式を自然数に翻訳して示す -/
  macro "translate" : tactic => `(tactic| with_reducible
    intros
    simp
    try ring
  )
end MyNat

namespace MyNat
  /- ## MyNat を AddCommMonoid のインスタンスにする -/

  instance : Zero MyNat where
    zero := ⟨0⟩

  /-- `MyNat` のゼロを自然数のゼロに翻訳する -/
  @[simp] theorem zero_val : (0 : MyNat).val = 0 := by rfl

  instance : AddCommMonoid MyNat where
    zero_add := by translate
    add_zero := by translate
    add_assoc := by translate
    add_comm := by translate
    nsmul := nsmulRec

end MyNat

namespace MyNat
  /- ## MyNat を CommSemiring のインスタンスにする -/

  instance : One MyNat where
    one := ⟨1⟩

  /-- `MyNat` の1を自然数の1に翻訳する -/
  @[simp] theorem one_val : (1 : MyNat).val = 1 := by rfl

  /-- `MyNat` は可換な半環(semiring)である -/
  instance : CommSemiring MyNat where
    left_distrib := by translate
    right_distrib := by translate
    zero_mul := by translate
    mul_zero := by translate
    one_mul := by translate
    mul_one := by translate
    mul_assoc := by translate
    mul_comm := by translate
end MyNat

example (m n : MyNat) : n * (n + m) = n * n + n * m := by
  -- `ring` が使えるようになった！
  ring
