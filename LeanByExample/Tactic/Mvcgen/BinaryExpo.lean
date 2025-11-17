import Lean

/-- 繰り返し自乗法で自然数の指数計算を行う -/
def binaryExpo (root n : Nat) : Nat := Id.run do
  let mut x := root
  let mut y := 1
  let mut e := n
  for _ in [0:n] do
    if e % 2 = 1 then
      y := x * y
      e := e - 1
    else
      x := x * x
      e := e / 2
    if e = 0 then
      break
  return y

open Std.Do

set_option mvcgen.warning false

@[grind =]
theorem Nat.Grind.pow_zero {n a : Nat} (h : a = 0) : n ^ a = 1 := by
  simp_all

@[grind =]
theorem Nat.pow_mul_self_halve_of_even (x e : Nat) (he : e % 2 = 0) :
    (x * x) ^ (e / 2) = x ^ e := calc
  _ = (x ^ 2) ^ (e / 2) := by grind
  _ = x ^ (2 * (e / 2)) := by grind [Nat.pow_mul]
  _ = x ^ e := by grind

@[grind! ·]
theorem Nat.mul_pow_sub_one_of_odd (x e : Nat) (he : e % 2 = 1) :
    x * x ^ (e - 1) = x ^ e := calc
  _ = x * x ^ (e - 1) := by grind
  _ = x ^ (1 + (e - 1)) := by grind
  _ = x ^ e := by congr; grind

theorem binaryExpo_spec (root n : Nat) :
    binaryExpo root n = root ^ n := by
  generalize h : binaryExpo root n = r
  apply Id.of_wp_run_eq h

  mvcgen invariants
  -- 不変条件の指定。
  -- ローカル可変変数は定義順ではなくアルファベット順に拘束されることに注意。
  · ⇓⟨cursor, e, x, y⟩ => ⌜y * x ^ e = root ^ n ∧ e + cursor.pos ≤ n⌝
  with grind
