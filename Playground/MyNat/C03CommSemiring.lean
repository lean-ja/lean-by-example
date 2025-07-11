import Playground.MyNat.C02MulAssoc

open Lean Grind

instance : NatCast MyNat where
  natCast := MyNat.ofNat

instance : HMul Nat MyNat MyNat where
  hMul := fun n m => MyNat.ofNat n * m

def MyNat.hPow (n : MyNat) (k : Nat) : MyNat :=
  match k with
  | 0 => 1
  | k + 1 => MyNat.hPow n k * n

instance : HPow MyNat Nat MyNat where
  hPow := MyNat.hPow

@[grind =, simp]
theorem MyNat.pow_zero (n : MyNat) : n ^ (0 : Nat) = 1 := by
  rfl

@[grind =]
theorem MyNat.pow_succ (n : MyNat) (k : Nat) :
    n ^ (k + 1) = n ^ k * n := by
  rfl

/-- MyNatは半環 -/
instance : Semiring MyNat where
  add := (· + ·)
  mul := (· * ·)
  add_zero := MyNat.add_zero
  add_assoc := MyNat.add_assoc
  add_comm := MyNat.add_comm
  mul_assoc := MyNat.mul_assoc
  left_distrib := MyNat.mul_add
  right_distrib := MyNat.add_mul
  zero_mul := MyNat.zero_mul
  mul_zero := MyNat.mul_zero
  one_mul := MyNat.one_mul
  mul_one := MyNat.mul_one
  pow_zero := MyNat.pow_zero
  pow_succ := MyNat.pow_succ

/-- MyNatは可換な半環 -/
instance : CommSemiring MyNat where
  mul_comm := MyNat.mul_comm

example (n : MyNat) : ∃ s t : MyNat, s * t = n * n + 8 * n + 16 := by
  exists (n + 4), (n + 4)
  grind
