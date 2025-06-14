/- # \#lint

`#lint` コマンドは、リンタ（よくない書き方をされたコードを指摘してくれるツール）を実行します。

-/
import Batteries.Tactic.Lint

-- ドキュメントコメントのない定理
theorem hoge : True := by trivial

-- ドキュメントコメントのない定理に対して警告するリンタ
/-⋆-//--
error: -- Found 1 error in 1 declarations (plus 0 automatically generated ones) in the current file with 1 linters

/- The `docBlameThm` linter reports:
THEOREMS ARE MISSING DOCUMENTATION STRINGS: -/
#check hoge /- theorem missing documentation string -/
-/
#guard_msgs (error) in --#
#lint only docBlameThm

-- ドキュメントコメントのない定義
def fuga : True := by trivial

-- 定義にドキュメントコメントがあるか確認するリンタ
-- 定理は対象外なのでスルーされる
/-⋆-//--
error: -- Found 1 error in 2 declarations (plus 0 automatically generated ones) in the current file with 1 linters

/- The `docBlame` linter reports:
DEFINITIONS ARE MISSING DOCUMENTATION STRINGS: -/
#check fuga /- definition missing documentation string -/
-/
#guard_msgs (whitespace := lax) in --#
#lint only docBlame
