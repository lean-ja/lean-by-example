import Lean

open Std.WP

/-- 繰り返し自乗法で自然数の指数計算を行う -/
def binaryExpo (root n : Nat) : Nat := Id.run do
  let mut x := root
  let mut y := 1
  let mut e := n
  while 0 < e do
    if e % 2 = 1 then
      y := x * y
      e := e - 1
    else
      x := x * x
      e := e / 2
  return y

#guard binaryExpo 2 10 = 1024
#guard binaryExpo 23 0 = 1

private theorem pow_zero_for_grind {n a : Nat} (h : a = 0) : n ^ a = 1 := by
  simp_all

grind_pattern pow_zero_for_grind => n ^ a where
  guard a = 0

@[grind =]
private theorem pow_mul_self_halve_of_even (x e : Nat) (he : e % 2 = 0) :
    (x * x) ^ (e / 2) = x ^ e := calc
  _ = (x ^ 2) ^ (e / 2) := by grind
  _ = x ^ (2 * (e / 2)) := by grind [Nat.pow_mul]
  _ = x ^ e := by grind

@[grind! ·]
private theorem mul_pow_sub_one_of_odd (x e : Nat) (he : 0 < e) :
    x * x ^ (e - 1) = x ^ e := calc
  _ = x ^ (1 + (e - 1)) := by grind
  _ = x ^ e := by grind

-- `vcgen` が実験的機能であることを明示する
set_option experimental.vcgen true in

theorem binaryExpo_spec (root n : Nat) : binaryExpo root n = root ^ n := by
  generalize h : binaryExpo root n = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · -- 不変条件を指定する。
    -- 継続中か終了後かを表すフラグに応じて、２つの不変条件を記述する。
    fun
    | false, (x, y, e) => y * x ^ e = root ^ n
    | true, (_, y, _) => y = root ^ n
  · -- while ループが停止することを保証するために
    -- e がループごとに減少していくと指定する
    Variant.ofMeasure fun (_, _, e) => e
  with finish
