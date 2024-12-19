/- # \#lint

`#lint` コマンドは、リンタ（よくない書き方をされたコードを指摘してくれるツール）を実行します。

たとえば、以下は「ドキュメントコメントのない定理に対して警告するリンタ」を実行する例です。
-/
import Batteries.Tactic.Lint

-- ドキュメントコメントのない定理
theorem hoge : True := by trivial

-- エラーにならない
/--
info: -- Found 0 errors in 1 declarations
(plus 0 automatically generated ones) in the current file with 1 linters

-- All linting checks passed!
-/
#guard_msgs (whitespace := lax) in
  -- 定義にドキュメントコメントがあるか確認するリンタ
  -- 定理は対象外なのでスルーされる
  #lint only docBlame

-- 技術的な理由で `#lint` の出力は省略しているが、
-- エラーになっている
#guard_msgs (drop error) in
  -- ドキュメントコメントのない定理に対して警告するリンタを実行している
  #lint only docBlameThm
