/-
# Problem 36
(Intermediate 🌟🌟) Determine the prime factors and their multiplicities of a given positive integer.

Construct a list containing each prime factor and its multiplicity.
-/

partial def primeFactorsMult (n : Nat) : List (Nat × Nat) :=
  loop 2 n [] |>.reverse
where
  /-- the multiplicity of `d` in `n` -/
  extract (d n : Nat) : Nat × Nat :=
    if d ≤ 1 then
      (1, 0)
    else if n % d != 0 then
      (d, 0)
    else
      let (d, m) := extract d (n / d)
      (d, m + 1)

  /-- helper function -/
  loop (d target : Nat) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    if target ≤ 1 then
      acc
    else
      let (d, m) := extract d target
      if m = 0 then
        loop (d + 1) target acc
      else
        loop (d + 1) (target / (d ^ m)) ((d, m) :: acc)

#guard primeFactorsMult 0 = []

#guard primeFactorsMult 1 = []

#guard primeFactorsMult 2 = [(2, 1)]

#guard primeFactorsMult 315 = [(3, 2), (5, 1), (7, 1)]

#guard primeFactorsMult 307 = [(307, 1)]

#guard primeFactorsMult 1000 = [(2, 3), (5, 3)]

#guard primeFactorsMult 990801529 = [(31477, 2)]

#guard primeFactorsMult 119883030485877764933
  = [(104623, 1), (104639, 2), (104651, 1)]
