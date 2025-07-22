/-
# Problem 37
(Intermediate 🌟🌟) Calculate Euler's totient function `φ(m)` (improved).

See [Problem 34](./Problem34.md) for the definition of Euler's totient function. If the list of the prime factors of a number `m` is known in the form of [Problem 36](./Problem36.md) then the function `φ(m)` can be efficiently calculated as follows: Let `[(p₁, m₁), (p₂, m₂), (p₃, m₃), ...]` be the list of prime factors (and their multiplicities) of a given number `m`. Then `φ(m)` can be calculated with the following formula:

$$
φ(m) = ∏_{i=1}^{n} (p_i - 1) * p_i^{(m_i - 1)}
$$
-/

/-- the list of prime factors and their multiplicities of `n` -/
abbrev PrimeFactor := List (Nat × Nat)

def φ (_n : Nat) (factors : PrimeFactor) : Nat :=
  factors.foldl (fun acc (p, m) => acc * (p - 1) * p ^ (m - 1)) 1

#guard φ 10 [(2, 1), (5, 1)] = 4

#guard φ 20 [(2, 2), (5, 1)] = 8

#guard φ 39 [(3, 1), (13, 1)] = 24
