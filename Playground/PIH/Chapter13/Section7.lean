import Playground.PIH.Chapter13.Section6

namespace Parser

  /-- 前後の空白を無視してトークンのパーサを適用する -/
  def token {α : Type} (p : Parser α) : Parser α := do
    let _ ← space
    let v ← p
    let _ ← space
    return v

  /-- 前後の空白を無視する識別子用パーサ -/
  def identifier : Parser String := token ident

  /-- 前後の空白を無視する自然数用パーサ -/
  def natural : Parser Nat := token nat

  /-- 前後の空白を無視する整数用パーサ -/
  def integer : Parser Int := token int

  /-- 前後の空白を無視する記号用パーサ -/
  def symbol (xs : String) : Parser String := token (string xs)

end Parser


namespace Parser

  /-- 空でない自然数のリストを解析するパーサー -/
  def nats : Parser (List Nat) := do
    let _ ← symbol "["
    let n ← natural
    let ns ← Alternative.many (do
      let _ ← symbol ","
      natural
    )
    let _ ← symbol "]"
    return (n :: ns)

  #guard nats "[1, 2, 3, 4, 5]" = some ([1, 2, 3, 4, 5], "")

  #guard nats "[1,  2,  3]" = some ([1, 2, 3], "")

  #guard nats "[1, 2,]" = none

end Parser
