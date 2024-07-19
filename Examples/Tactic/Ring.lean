/- # ring

`ring` は、可換環の等式を示します。ローカルコンテキストの仮定は読まず、環の公理だけを使います。-/
import Mathlib.Tactic.Ring -- `ring` のために必要

variable (x y z : ℤ)

example : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

example (hz : z = x + y) : x * z = x ^ 2 + x * y := by
  -- `ring` はローカルコンテキストの仮定を読まないので、これは通らない
  ring
  show x * z = x * y + x ^ 2

  -- `rw` などで、環の公理だけを使って示せる形にすれば OK
  rw [hz]
  ring

/-! ## ring_nf
`ring` は等式を示そうとするタクティクですが、`ring_nf` は式を整理して標準形と呼ばれる形にします。
-/
example {x y z : Rat} (h : z = (x + y) ^ 2) : z = x ^ 2 + 2 * x * y + y ^ 2 := by
  -- `(x + y) ^ 2` を展開する
  ring_nf at h

  -- `h` を代入して `z` を消去する
  rw [h]

  -- 後は可換環の公理から示せる
  ring

/-! ## 環でないものに ring を使ったら

たとえば自然数 `ℕ` は環ではありません。そのため、自然数の引き算などを含む式は多くの場合 `ring` では示せません。代わりに `ring_nf` を使うように促されますが、`ring_nf` でも示せるとは限りません。
-/

-- Lean では自然数の引き算は
-- `n ≤ m` のとき `n - m = 0` になるように定義されている
example : 7 - 42 = 0 := rfl

-- 整数にすると結果が変わる
example : 7 - (42 : ℤ) = - 35 := rfl

/-- info: Try this: ring_nf -/
#guard_msgs in
example {n : Nat} : n - n + n = n := by
  -- `ring_nf` を提案される
  try ring

  simp

example {n : Nat} : n - n + n = n := by
  -- 提案通りに `ring_nf` を使っても効果なし
  ring_nf
  show n - n + n = n

  simp

/-! ## ring の中身を見る方法

`simp` 等と異なり、`ring?` タクティクは用意されていませんが、`show_term` で具体的にどんなルールが適用されたのかを知ることができます。
ただし、その出力結果は非常に長く読みづらいものであることがしばしばです。
-/

example : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
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
