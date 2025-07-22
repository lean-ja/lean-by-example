/-
# 問題 25
(初級 🌟) リストの要素のランダムな順列を生成せよ。
-/
variable {α : Type} [Inhabited α] [BEq α]

/-- 与えられたリストからランダムに1要素を取り除き、その要素と残りのリストを返す -/
def List.extractOne (univ : List α) : IO (Option α × List α) := do
  if univ == [] then
    return (none, [])

  let index ← IO.rand 0 (univ.length - 1)
  let element := univ[index]!
  let rest := univ.take index ++ univ.drop (index + 1)
  return (element, rest)

partial def rndPermu (l : List α) : IO (List α) := do
  let (element, rest) ← l.extractOne
  match element with
  | none => return []
  | some e =>
    return e :: (← rndPermu rest)

-- テスト例（#eval で確認）
def runTest [ToString α] (l : List α) : IO Unit := do
  let result ← rndPermu l
  let check := result.isPerm l

  if l.length >= 30 then
    let result' ← rndPermu l
    if result == result' then
      throw <| .userError "failed: Your function is not random."

  if check then
    IO.println "ok!"
  else
    throw <| .userError s!"failed: rndPermu {l} = {result}"

#eval runTest [1, 2, 3]
#eval runTest ['a', 'a', 'a']
#eval runTest ([] : List Nat)
#eval runTest (List.range 35)
