/- # syntax
`syntax` コマンドは新しい構文を定義することができます。
-/
import Lean

open Lean Parser

/-- parse できるかどうかチェックする関数 -/
def checkParse (cat : Name) (s : String) : MetaM Unit := do
  if let .error s := runParserCategory (← getEnv) cat s then
    throwError s

-- 最初は `#greet` などというコマンドは定義されていないので
-- そもそも Lean の合法な構文として認められない。
/-- error: <input>:1:0: expected command -/
#guard_msgs (error) in
  #eval checkParse `command "#greet"

-- `#greet` というコマンドのための構文を定義
syntax "#greet" : command

-- `#greet` というコマンドが Lean に認識されるようになった。
-- エラーメッセージは、`#greet` コマンドの解釈方法がないと言っている。
/-- error: elaboration function for '«command#greet»' has not been implemented -/
#guard_msgs in #greet

/- Lean に構文を認識させるだけでなく、解釈させるには [`macro_rules`](./MacroRules.md) などの別のコマンドが必要です。-/

-- `#greet` コマンドの解釈方法を定める
macro_rules
  | `(command| #greet) => `(#eval "Hello, Lean!")
