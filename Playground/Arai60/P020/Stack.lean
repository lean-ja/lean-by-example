/-
文字列 `s` が `'('`, `')'`, `'{'`, `'}'`, `'['`, `']'` のみから構成されているとき、その文字列が**有効かどうか**を判定してください。

文字列が有効である条件は以下のとおりです：

* 開き括弧は同じ種類の閉じ括弧で閉じられなければならない。
* 開き括弧は正しい順序で閉じられなければならない。
* すべての閉じ括弧には、それに対応する同じ種類の開き括弧が存在しなければならない。
-/

-- 配列の末尾に要素を追加する関数
#check Array.push

-- 配列から最後の要素を取り出す関数
#check Array.back?

-- 配列の最後の要素を削除する関数
#check Array.pop

def matchParen (c1 c2 : Char) : Bool :=
  match c1, c2 with
  | '(', ')' => true
  | '{', '}' => true
  | '[', ']' => true
  | _, _ => false

-- **TODO** 配列をスタックとして使ういい例だと思われる
def validParen (s : String) : Bool := Id.run do
  let mut stack : Array Char := #[]
  for c in s.toList do
    let last := stack.back?
    match last with
    | none =>
      stack := stack.push c
    | some last =>
      if matchParen last c then
        stack := stack.pop
      else
        stack := stack.push c
  return stack.isEmpty

#guard validParen "()"        -- true
#guard validParen "()[]{}"    -- true
#guard !validParen "(]"       -- false
#guard !validParen "([)]"     -- false
#guard validParen "{[]}"      -- true
#guard !validParen "{"        -- false
#guard !validParen "}"        -- false
#guard validParen "([{}])({}){}"   -- true
