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

open Std.WP

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
  _ = x ^ (1 + (e - 1)) := by grind
  _ = x ^ e := by congr; grind

-- `vcgen` が実験的機能であることを明示する
set_option experimental.vcgen true in

theorem binaryExpo_spec (root n : Nat) :
    binaryExpo root n = root ^ n := by
  generalize h : binaryExpo root n = r
  apply Id.of_run_eq_wp h

  vcgen invariants
  -- 不変条件の指定。
  -- `pref` は処理済みの要素のリストで、その長さがループの反復回数に一致する
  -- ローカル可変変数は定義順に拘束される。
  · fun pref _ (x, y, e) => y * x ^ e = root ^ n ∧ e + pref.length ≤ n
  with finish
