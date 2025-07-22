/- # Problem 40

(Intermediate 🌟🌟) Goldbach's conjecture says that every positive even number greater than `2` is the sum of two prime numbers. Example: `28 = 5 + 23`. It is one of the most famous facts in number theory that has not been proved to be correct in the general case. It has been numerically confirmed up to very large numbers (much larger than we can go with our Prolog system). Write a predicate to find the two prime numbers that sum up to a given even integer.
-/

def Nat.isPrime (n : Nat) : Bool := Id.run do
  if n ≤ 2 then
    return false
  for d in [2:n] do
    if n % d = 0 then
      return false
    if d ^ 2 > n then
      break
  return true

-- You can use this!
#check Nat.isPrime

def goldbach (n : Nat) : Nat × Nat := Id.run do
  if n % 2 ≠ 0 then
    panic! "n must be an even number"

  for cand in [2:n] do
    if not cand.isPrime then
      continue
    let rest := n - cand
    if not rest.isPrime then
      continue
    return (cand, rest)

  panic! "we've found a counter example of goldbach conjecture!! 🎉"

def goldbachTest (n : Nat) : IO Unit :=
  let (fst, snd) := goldbach n
  if fst + snd ≠ n then
    throw <| .userError s!"failed: {fst} + {snd} ≠ {n}"
  else if ! fst.isPrime || ! snd.isPrime then
    throw <| .userError s!"failed: {fst} and {snd} must be prime."
  else
    IO.println s!"ok! {n} = {fst} + {snd}"

#eval goldbachTest 14

#eval goldbachTest 308

#eval goldbachTest 308000

#eval goldbachTest 19278020
