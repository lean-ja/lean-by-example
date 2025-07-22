/-
# 問題 33
(初級 🌟) 2つの正の整数が互いに素かどうか判定せよ。
-/

-- これは使ってよい
#check Nat.gcd

def coprime (a b : Nat) : Bool :=
  Nat.gcd a b = 1

#guard coprime 35 64 == true
#guard coprime 38859 233153 == true
#guard coprime 10284412 24135577 == true
