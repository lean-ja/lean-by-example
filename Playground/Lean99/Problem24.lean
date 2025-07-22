/-
# 問題 24
(初級 🌟) ロト: 1からMまでの集合からN個の異なるランダムな数を抽出せよ。
-/
import Lean

/-- 1からnまでの自然数のリストを生成する -/
def List.nrange (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | 1 => [1]
  | n + 1 => nrange n ++ [n + 1]

#guard List.nrange 5 == [1, 2, 3, 4, 5]


def diffSelect (count range : Nat) : IO (List Nat) := do
  if count > range then
    IO.println s!"can't draw {count} different numbers from 1..{range}"
    return []

  let mut univ := List.nrange range
  let mut result : List Nat := []
  for _ in [0 : count] do
    let (element, rest) ← extractOne univ
    if let some e := element then
      univ := rest
      result := e :: result

  return result
where
  extractOne (univ : List Nat) : IO (Option Nat × List Nat) := do
    if univ == [] then
      return (none, [])

    let index ← IO.rand 0 (univ.length - 1)
    let element := univ[index]!
    let rest := univ.take index ++ univ.drop (index + 1)
    return (element, rest)

-- テスト例（#eval で確認）
def runTest (count range : Nat) : IO Unit := do
  let result ← diffSelect count range
  let check := result.eraseDups.length == count
    |> (· && result.all (List.nrange range).contains)
  if check then
    IO.println "ok!"
  else
    throw <| .userError s!"failed: diffSelect {count} {range} = {result}"

#eval runTest 3 3
#eval runTest 1 1
#eval runTest 2 2
#eval runTest 6 49
#eval runTest 1998 1999
#eval runTest 5668 5998
