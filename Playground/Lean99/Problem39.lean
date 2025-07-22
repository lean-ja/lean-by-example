/- # Problem 39

(Easy 🌟) Given a range of integers by its lower and upper limit, construct a list of all prime numbers in that range.
-/

/-- eratosthenes sieve -/
def eratosthenes (n : Nat) : Array Bool := Id.run do
  let mut isPrime := Array.replicate (n + 1) true

  isPrime := isPrime.set! 0 false
  isPrime := isPrime.set! 1 false

  for p in [2 : n + 1] do
    if not isPrime[p]! then
      continue

    if p ^ 2 > n then
      break

    let mut q := p * p
    while q <= n do
      isPrime := isPrime.set! q false
      q := q + p

  return isPrime

/-- Returns a list of prime numbers less than or equal to n given -/
def primeSieve (n : Nat) : List Nat :=
  let result := eratosthenes n
  result.toList.zipIdx
    |> List.filter (fun (i, _e) => i)
    |> List.map (fun (_i, e) => e)

def primesR (s t : Nat) : List Nat :=
  primeSieve t |>.filter (· ≥ s)

#guard primesR 10 10 = []

#guard primesR 11 11 = [11]

#guard primesR 1 10 = [2, 3, 5, 7]

#guard primesR 30 100 = [31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
