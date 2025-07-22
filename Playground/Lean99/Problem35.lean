/-
# 問題 35
(中級 🌟🌟) 与えられた正の整数の素因数分解を求めよ。

素因数を昇順で平坦なリストとして返すこと。
-/

partial def primeFactors (n : Nat) : List Nat :=
  loop n 2 [] |>.reverse
where
  loop (tgt candidate : Nat) (acc : List Nat) : List Nat :=
    if tgt ≤ 1 || candidate > tgt then
      acc
    else if tgt % candidate = 0 then
      loop (tgt / candidate) candidate <| candidate :: acc
    else
      loop tgt (candidate + 1) acc

#guard primeFactors 17 == [17]
#guard primeFactors 315 == [3, 3, 5, 7]
#guard primeFactors 65536 == [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
#guard primeFactors 20063 == [20063]
#guard primeFactors 627537863 == [24137, 25999]
#guard primeFactors 10963345907 == [104683, 104729]
