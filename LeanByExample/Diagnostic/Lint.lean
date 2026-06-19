/- # \#lint

`#lint` コマンドは、環境リンター(environment linter)を実行します。

環境リンターとは何かというと、Lean のリンター（よくない書き方のコードを検出するツール）の一種です。
環境リンターは、`#lint` コマンドや `lake lint` コマンドで実行することができます。

Lean のリンターには他に、[構文リンター(syntax linter)](#{root}/Type/Linter.md)があります。
-/
import Batteries.Tactic.Lint

-- ドキュメントコメントのない定理
theorem hoge : True := by trivial

-- ドキュメントコメントのない定理に対して警告するリンタ
/--
The `docBlameThm` linter reports:
THEOREMS ARE MISSING DOCUMENTATION STRINGS:
-/
#guard_msgs (error, substring := true) in --#
#lint only docBlameThm

set_option linter.defProp false in --#
-- ドキュメントコメントのない定義
def fuga : True := by trivial

-- 定義にドキュメントコメントがあるか確認するリンタ
-- 定理は対象外なのでスルーされる
/--
The `docBlame` linter reports:
DEFINITIONS ARE MISSING DOCUMENTATION STRINGS:
-/
#guard_msgs (whitespace := lax, substring := true) in --#
#lint only docBlame

/-
環境リンターをユーザが自作したい場合は、`Batteries.Tactic.Lint.Linter` 型の項を作って `[env_linter]` 属性を付与します。
-/

open Lean Batteries Tactic Lint

/-- `bad` という文字が入っている宣言を検出する、意味のないリンター -/
@[env_linter]
meta def findBad : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "no bad declarations found."
  errorsFound := "BAD DECLARATIONS FOUND:"
  test declName := do
    -- 自動生成された宣言などを無視したければここで除外
    if ← isAutoDecl declName then
      return none

    -- declName を調べる
    let info ← getConstInfo declName

    -- 問題なしなら none
    -- 問題ありなら some メッセージ
    if info.name.toString.contains "bad" then
      return some m!"declaration name contains `bad`"
    else
      return none

def bad := "わるいよ！"

/--
error: -- Found 1 error in 4 declarations (plus 0 automatically generated ones) in the current file with 1 linters
-/
#guard_msgs (substring := true) in --#
#lint only findBad
