/- # syntax

[`🏷️メタプログラミング`](./?search=🏷メタプログラミング)

`syntax` コマンドは新しい構文を定義することができます。
-/
import Lean
namespace Syntax --#

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
/-- error: elaboration function for 'Syntax.«command#greet»' has not been implemented -/
#guard_msgs in #greet

/- Lean に構文を認識させるだけでなく、解釈させるには [`macro_rules`](./MacroRules.md) などの別のコマンドが必要です。-/

-- `#greet` コマンドの解釈方法を定める
macro_rules
  | `(command| #greet) => `(#eval "Hello, Lean!")

/- ## パース優先度
`syntax` コマンドは Lean に新しい構文解析ルールを追加するので、既存の構文と衝突して意図通りに解釈されないことがあります。
-/
section

/-- `a = b as T` という構文を定義 -/
local syntax term " = " term " as " term : term

/-- `a = b as T` という構文を、型 `T` 上で `a = b` が成り立つと解釈させる -/
local macro_rules
  | `(term| $a = $b as $c) => `(@Eq (α := $c) $a $b)

-- `Nat` と `Prop` を足すことはできないというエラーメッセージ。
-- `1 + (1 = 2)` だと認識されてしまっているようだ。
/--
warning: failed to synthesize
  HAdd Nat Prop ?m.1897
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs (warning) in
  #check_failure (1 + 1 = 2 as Nat)

end
/- パース優先度(parsing precedence)を設定することで、どの構文から順に解釈されるかを指定することができ、問題を修正できることがあります。このあたりは [`notation`](./Notation.md) コマンドと同様です。 -/
section

-- 十分低いパース優先度を設定する
local syntax:10 term:10 " = " term:10 " as " term:10 : term

local macro_rules
  | `(term| $a = $b as $c) => `(@Eq (α := $c) $a $b)

-- 意図通りに構文解析が通るようになる
#guard (1 + 1 = 2 as Nat)

#guard (3 - 5 + 4 = 2 as Int)

#guard (2 * 3 / 2 = 3 as Rat)

end
end Syntax --#
