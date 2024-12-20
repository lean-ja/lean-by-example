/- # ring

`ring` は、可換環の等式を示します。ローカルコンテキストの仮定は読まず、環の公理だけを使います。-/
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

/- 自然数 `Nat` は半環(環の条件のうちマイナスがあるという条件を満たさないもの)ですが、`ring` は可換な半環に対しても使用することができるので自然数の和と積についての式は `ring` で示すことができます。-/

example (n m : Nat) : (n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2 := by
  ring

example (n m : Nat) : n * (n + m) = n ^ 2 + n * m := by
  ring

/- ## ring の中身を見る方法

`simp` 等と異なり、`ring?` タクティクは用意されていませんが、`show_term` で具体的にどんなルールが適用されたのかを知ることができます。
ただし、その出力結果は非常に長く読みづらいものであることがしばしばです。
-/
set_option linter.unusedTactic false in --#

example (x y : Int) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  try
    /-
      以下のような出力が100行以上続く
      Try this: exact Mathlib.Tactic.Ring.of_eq
      (Mathlib.Tactic.Ring.pow_congr
        ...
    -/
    show_term ring

    fail

  ring
