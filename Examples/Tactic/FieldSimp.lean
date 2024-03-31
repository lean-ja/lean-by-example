/-
# field_simp

`field_simp` は，「分母を払う」操作に対応するタクティクです．
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith --#
import Mathlib.Tactic.Ring

example (n m : Rat) : n * m = ((n + m) ^ 2 - n ^ 2 - m ^ 2 ) / 2 := by
  -- 分母を払う
  field_simp

  -- Rat は可換環なので， 示すべきことが言える
  ring

/-! 分母がゼロでないことが判らない場合は動作しません．分母がゼロでないことを証明してローカルコンテキストに加えると動作することがあります．-/

example {x y z : Rat} (hy : y = z ^ 2 + 1) : (x + 2 * y) / y = x / y + 2 := by
  -- まず分母がゼロでないことを示す
  have ypos : y ≠ 0 := by
    rw [hy]
    nlinarith

  -- 分母を払う
  field_simp

/-! また，`field_simp` という名前の通り，割り算が体の割り算でなければ動作しないことがあります．たとえば 自然数 `Nat` における割り算は `field_simp` では簡約することができず，次のコード例のように工夫する必要があります．-/

example (n m : Nat) : n * m = ((n + m) ^ 2 - n ^ 2 - m ^ 2 ) / 2 := by
  -- field_simp は動作しない
  fail_if_success field_simp

  -- 分母を払う
  symm
  apply Nat.div_eq_of_eq_mul_right (by simp_arith)

  -- `(n + m) ^ 2` を展開する
  rw [show (n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2 from by ring]

  -- 打消し合う項を消して簡単にすれば，示すべきことが言える
  simp [add_assoc, mul_assoc]
