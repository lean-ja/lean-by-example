import Lean

set_option mvcgen.warning false

open Std.Do

/-- 農民の掛け算。２で割る操作と２倍する操作と足し算だけで掛け算を行う -/
def peasantMul (x y : Nat) : Nat := Id.run do
  let mut curX := x
  let mut curY := y
  let mut prod := 0
  for _ in [0:x] do
    if curX = 0 then
      break
    if curX % 2 = 1 then
      prod := prod + curY
    curX := curX / 2
    curY := curY * 2
  return prod

attribute [grind =] Nat.div_div_eq_div_mul

@[grind ->]
theorem div2_mul2_odd (x : Nat) (odd : x % 2 = 1) : x = (x / 2) * 2 + 1 := by
  grind

@[grind ->]
theorem div2_mul2_even (x : Nat) (even : x % 2 = 0) : x = (x / 2) * 2 := by
  grind

@[grind =, simp]
theorem div_pow_self_two_eq_zero (n : Nat) : n / 2 ^ n = 0 := by
  have : n < 2 ^ n := Nat.lt_two_pow_self
  simp_all

example (x y : Nat) : peasantMul x y = x * y := by
  generalize h : peasantMul x y = s
  apply Id.of_wp_run_eq h

  mvcgen invariants
  · ⇓⟨cursor, curX, curY, prod⟩ =>
    ⌜curX = x / 2 ^ cursor.pos ∧ curX * curY + prod = x * y⌝
  with (simp at * <;> grind)
