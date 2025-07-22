/-
# 問題 40
(中級 🌟🌟) ゴールドバッハの予想：「2より大きいすべての偶数は2つの素数の和で表せる」。例: 28 = 5 + 23。これは数論で最も有名な未解決問題の一つであり、一般の場合の証明はないが非常に大きな数まで数値的に確認されている。与えられた偶数を2つの素数の和として表すペアを求めよ。
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

-- これを使ってよい
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
