/-
# 問題 34
(中級 🌟🌟) オイラーのトーシェント関数 φ(m) を計算せよ。

オイラーのトーシェント関数 φ(m) は、1 <= r < m で m と互いに素な正整数 r の個数である。

例: m = 10 のとき r = 1, 3, 7, 9 なので φ(10) = 4。特別な場合 φ(1) = 1。
-/

def totient (m : Nat) : Nat :=
  let coprimes := List.range (m + 1)
    |>.drop 1
    |>.filter (Nat.gcd · m == 1)
  coprimes.length

#guard totient 1 == 1
#guard totient 10 == 4
#guard totient 7 == 6
#guard totient 70 == 24
