/-
# 問題 23
(中級 🌟🌟) リストから指定個数のランダムな要素を抽出せよ。
-/
import Lean
namespace P23

variable {α : Type} [Inhabited α]

def rndSelect (l : List α) (n : Nat) : IO (List α) := do
  match l, n with
  | [], _ => pure []
  | _, 0 => pure []
  | _, n + 1 =>
    let index ← IO.rand 0 $ l.length - 1
    let previous ← rndSelect l n
    pure <| l[index]! :: previous

-- テスト例（#eval で確認）
def runTest [BEq α] [ToString α] (l : List α) (n : Nat) : IO Unit := do
  let result ← rndSelect l n
  let check := result.length == n
    |> (· && result.all l.contains)
  if check then
    IO.println s!"ok!"
  else
    throw <| .userError s!"failed: rndSelect {l} {n} = {result}"

#eval runTest [1, 2, 3] 0
#eval runTest ['a', 'b'] 1
#eval runTest [1, 2, 3, 4, 5] 2
#eval runTest [1, 1, 1] 2
#eval runTest [2, 2, 2] 12
#eval runTest (List.range 5200) 1897

end P23
