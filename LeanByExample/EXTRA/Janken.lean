/- # じゃんけんゲーム

じゃんけんゲームを CLI で実装する例を紹介します。
-/

/-- ユーザからの入力を受け取る -/
def getUserInput : IO String := do
  -- 入力待ちを表す記号を表示
  IO.print "> "

  let stdin ← IO.getStdin
  let input ← stdin.getLine
  return input.trimAscii.copy

/-- じゃんけんの手 -/
inductive Hand where
  /-- グー -/
  | gu
  /-- チョキ -/
  | choki
  /-- パー -/
  | pa
deriving BEq, Inhabited

protected def Hand.toString : Hand → String
  | .gu => "グー"
  | .choki => "チョキ"
  | .pa => "パー"

instance : ToString Hand := ⟨Hand.toString⟩

/-- 文字列を読んで Hand に変換する -/
def parseHand (input : String) : Option Hand :=
  match input with
  | "グー" => some Hand.gu
  | "チョキ" => some Hand.choki
  | "パー" => some Hand.pa
  | _ => none

/-- h1 が h2 に勝つかどうかを判定する -/
def beat (h1 h2 : Hand) : Bool :=
  match h1, h2 with
  | .gu, .choki => true
  | .choki, .pa => true
  | .pa, .gu => true
  | _, _ => false

/-- ランダムに手を選ぶ -/
def getRandomHand : IO Hand := do
  let n ← IO.rand 1 3
  let hand :=
    match n with
    | 1 => Hand.gu
    | 2 => Hand.choki
    | 3 => Hand.pa
    | _ => unreachable!
  return hand

def main : IO Unit := do
  IO.println "私とじゃんけんをしよう！"
  IO.println "グー、チョキ、パーのどれかを選んで！"

  let mut finish := false
  while !finish do
    let userInput ← getUserInput

    let some yourHand := parseHand userInput |
      IO.println "そんな手はないよ！もう一回！"
      continue

    let cpuHand ← getRandomHand
    IO.println s!"私は{cpuHand}を出したよ！"

    if yourHand == cpuHand then
      IO.println "あいこだね！もう一勝負！"
    else if beat yourHand cpuHand then
      IO.println "あなたの勝ち！負けちゃったなぁ"
      finish := true
    else
      IO.println "私の勝ち！うれしい！"
      finish := true
