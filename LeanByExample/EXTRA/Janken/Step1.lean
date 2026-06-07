import LeanByExample.EXTRA.Janken --#

def main : IO Unit := do
  IO.println "私とじゃんけんをしよう！"
  IO.println "グー、チョキ、パーのどれかを選んで！"
  let yourHand ← getUserHand
  IO.println s!"{yourHand}を選んだんだね！"
