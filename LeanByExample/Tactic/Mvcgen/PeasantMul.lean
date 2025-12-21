import Lean

set_option mvcgen.warning false

open Std.Do

/-- 農民の掛け算。２で割る操作と２倍する操作と足し算だけで掛け算を行う -/
def peasantMul (x y : Nat) : Nat := Id.run do
  let mut curX := x
  let mut curY := y
  let mut prod := 0
  for _ in [0:x] do
    if curX % 2 = 1 then
      prod := prod + curY
    curX := curX / 2
    curY := curY * 2
    if curX = 0 then
      break
  return prod

theorem Nat.div_pow_add (x a b c : Nat) : x / c ^ (a + b) = (x / c ^ a) / c ^ b := by
  grind [Nat.div_div_eq_div_mul, Nat.pow_add]

-- 左辺をみかけたらインスタンス化する
-- ただし a, b, c が 0 や 1 になっているときは(無駄なので)インスタンス化しない
grind_pattern Nat.div_pow_add => x / c ^ (a + b) where
  a =/= 0
  b =/= 0
  c =/= 0
  c =/= 1

-- a / b を見かけたらインスタンス化する
grind_pattern Nat.div_add_mod' => a / b where
  not_value a
  is_value b
  b =/= 0
  b =/= 1

@[grind =]
theorem Nat.div_pow_self_two_eq_zero (n : Nat) : n / 2 ^ n = 0 := by
  have : n < 2 ^ n := Nat.lt_two_pow_self
  simp_all

example (x y : Nat) : peasantMul x y = x * y := by
  generalize h : peasantMul x y = s
  apply Id.of_wp_run_eq h

  mvcgen invariants
  · ⇓⟨cursor, curX, curY, prod⟩ =>
    ⌜curX = x / 2 ^ cursor.pos ∧ curX * curY + prod = x * y⌝
  with (simp at * <;> grind)
