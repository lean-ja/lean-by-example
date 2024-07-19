/-
# field_simp
`field_simp` は、体における等式を示す際の「分母を払う」操作に対応するタクティクです。
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith --#
import Mathlib.Tactic.Ring

example (n m : Rat) : n * m = ((n + m) ^ 2 - n ^ 2 - m ^ 2 ) / 2 := by
  -- 分母を払う
  field_simp

  -- Rat は可換環なので、 示すべきことが言える
  ring

/-! 分母がゼロでないことが判らない場合は動作しません。分母がゼロでないことを証明してローカルコンテキストに加えると動作することがあります。-/

example {x y z : Rat} (hy : y = z ^ 2 + 1) : (x + 2 * y) / y = x / y + 2 := by
  -- 最初 `field_simp` は動作しない
  fail_if_success field_simp

  -- 分母がゼロでないことを示す
  have ypos : y ≠ 0 := by
    rw [hy]
    nlinarith

  -- 動作するようになった
  field_simp

/-! ## 制約
`field_simp` という名前の通り、割り算が体の割り算でなければ動作しません。たとえば 自然数 `Nat` における割り算は `field_simp` では扱うことができず、次のコード例のように工夫する必要があります。-/

example (n m : Nat) : n * m = ((n + m) ^ 2 - n ^ 2 - m ^ 2 ) / 2 := by
  -- field_simp は動作しない
  fail_if_success field_simp

  -- 分母を払う
  symm
  apply Nat.div_eq_of_eq_mul_right (by simp_arith)

  -- `(n + m) ^ 2` を展開する
  rw [show (n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2 from by ring]

  -- 打消し合う項を消して簡単にすれば、示すべきことが言える
  simp [add_assoc, mul_assoc]

/- また `field_simp` の扱うのは等式のみで、順序関係は扱いません。体の定義に順序関係は含まれていないので、体を扱うタクティクとしては自然なことかもしれません。-/

variable (x y : Rat)

example : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
  -- 何も起こらない
  fail_if_success field_simp

  suffices x ^ 2 - 2 * x * y + y ^ 2 ≥ 0 from by
    linarith
  calc
    x ^ 2 - 2 * x * y + y ^ 2 = (x - y) ^ 2 := by ring
    _ ≥ 0 := by apply sq_nonneg

example (h : x = y) : x * y = (x ^ 2 + y ^ 2) / 2 := by
  -- 等式ならば扱える
  field_simp

  -- ゴールの分母を払うことができた
  show x * y * 2 = x ^ 2 + y ^ 2

  rw [h]
  ring
