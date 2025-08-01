import Batteries.Data.MLList.Basic

/-- 遅延評価のリスト -/
abbrev LazyList := MLList Id

/-- 与えられた自然数が素数かどうか判定する -/
def Nat.isPrime (n : Nat) : Bool := Id.run do
  if n ≤ 1 then
    return false
  if n = 2 then
    return true
  for d in [2:n] do
    if n % d = 0 then
      return false
    if d ^ 2 > n then
      break
  return true

#guard
  let actual := (List.range 100).filter Nat.isPrime
  let expected := [
    2, 3, 5, 7, 11,
    13, 17, 19, 23, 29,
    31, 37, 41, 43, 47,
    53, 59, 61, 67, 71,
    73, 79, 83, 89, 97
  ]
  actual == expected

def goldbach (n : Nat) (_ : n % 2 = 0 := by decide) : Nat × Nat :=
  let candidates : LazyList (Nat × Nat) := MLList.range
    |>.filter (· ≤ n)
    |>.filter Nat.isPrime
    |>.filter (fun x => (n - x).isPrime)
    |>.map (fun x => (x, n - x))
  candidates.head? |>.get!

#time #eval goldbach 123456

def goldbach' (n : Nat) (_ : n % 2 = 0 := by decide) : Nat × Nat :=
  let candidates : List (Nat × Nat) := List.range n
    |>.filter Nat.isPrime
    |>.filter (fun x => (n - x).isPrime)
    |>.map (fun x => (x, n - x))
  candidates.head!

#time #eval goldbach' 123456
