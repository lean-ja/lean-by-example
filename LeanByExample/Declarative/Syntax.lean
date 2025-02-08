/- # syntax

`syntax` コマンドは新しい構文を定義することができます。
-/
import Lean

open Lean Parser

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

-- 最初は `#greet` などというコマンドは定義されていないので
-- そもそも Lean の合法な構文として認められない。
/-- error: <input>:1:0: expected command -/
#guard_msgs (error) in
  #eval parse `command "#greet"

-- `#greet` というコマンドのための構文を定義
syntax "#greet" : command

-- まだエラーになるが、少なくとも `#greet` というコマンドが Lean に認識されるようにはなった。
-- エラーメッセージは、`#greet` コマンドの解釈方法がないと言っている。
/-⋆-//-- error: elaboration function for '«command#greet»' has not been implemented -/
#guard_msgs in --#
#greet

/- Lean に構文を認識させるだけでなく、解釈させるには [`macro_rules`](./MacroRules.md) などの別のコマンドが必要です。-/

-- `#greet` コマンドの解釈方法を定める
macro_rules
  | `(command| #greet) => `(#eval "Hello, Lean!")

/-⋆-//-- info: "Hello, Lean!" -/
#guard_msgs in --#
#greet

/- ## パース優先順位
`syntax` コマンドは Lean に新しい構文解析ルールを追加しますが、導入した構文が意図通りに解釈されないことがあります。
-/
section

  /-- `a = b as T` という構文を定義 -/
  local syntax term " = " term " as " term : term

  /-- `a = b as T` という構文を、型 `T` 上で `a = b` が成り立つと解釈させる -/
  local macro_rules
    | `(term| $a = $b as $c) => `(@Eq (α := $c) $a $b)

  -- メタ変数の番号を表示しない
  set_option pp.mvars false

  -- `1 + (1 = 2)` だと認識されてしまっている
  /-- info: 1 + (1 = 2) : ?_ -/
  #guard_msgs (info, drop error) in
    #check (1 + 1 = 2 as Nat)

end
/- **パース優先順位(parsing precedence)** を設定することで、どの構文から順に解釈されるかを指定することができ、問題を修正できることがあります。このあたりは [`notation`](./Notation.md) コマンドと同様です。 -/
section

  -- 十分低いパース優先順位を設定する
  local syntax:10 term:10 " = " term:10 " as " term:10 : term

  local macro_rules
    | `(term| $a = $b as $c) => `(@Eq (α := $c) $a $b)

  -- 意図通りに構文解析が通るようになる
  #guard (1 + 1 = 2 as Nat)

  #guard (3 - 5 + 4 = 2 as Int)

  -- Nat だと 3 - 5 = 0 となるので結果が変わる
  #guard (3 - 5 + 4 = 4 as Nat)
end
/- ## name 構文
`(name := ...)` という構文により、名前を付けることができます。名前を付けると、その名前で `Lean.ParserDescr` の項が生成されます。
-/

-- 最初は存在しない
#check_failure (hogeCmd : ParserDescr)

-- `#hoge` というコマンドを定義する
-- `name` 構文で名前を付けることができる
syntax (name := hogeCmd) "#hoge" : command

-- 構文に対して付けた名前で、ParserDescr 型の項が生成されている
#check (hogeCmd : ParserDescr)
