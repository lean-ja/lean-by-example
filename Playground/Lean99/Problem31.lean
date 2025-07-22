/-
# 問題 31
(中級 🌟🌟) 与えられた自然数が素数かどうか判定せよ。
-/

def isPrime (n : Nat) : Bool :=
  if n == 0 || n == 1 then
    false
  else
    let properDivisors := List.range n
      |>.drop 2
      |>.filter (n % · == 0)

    properDivisors.length == 0

#guard isPrime 7 == true
#guard isPrime (7 * 43) == false
#guard isPrime 307 == true
#guard isPrime 0 == false
#guard isPrime 1 == false
