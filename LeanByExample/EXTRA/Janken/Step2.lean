import LeanByExample.EXTRA.Janken --#

open Hand

def main : IO Unit := do
  IO.println "私とじゃんけんをしよう！"
  IO.println "グー、チョキ、パーのどれかを選んで！"

  let mut finish := false
  while !finish do
    let yourHand ← getUserHand

    let cpuHand ← getRandomHand
    IO.println s!"私は{cpuHand}を出したよ！"

    if beat yourHand cpuHand then
      IO.println "あなたの勝ち！負けちゃったなぁ"
      finish := true
    else if beat cpuHand yourHand then
      IO.println "私の勝ち！うれしい！"
      finish := true
    else
      IO.println "あいこだね！もう一勝負！"
