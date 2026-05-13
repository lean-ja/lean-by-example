/- # \#lint

`#lint` コマンドは、environment linter を実行します。
environment linter は、elaboration 後に environment に登録された定義・定理・インスタンスなどを検査するリンタです。
たとえば「ドキュメントコメントが足りない」「`[simp]` 補題として危険」といった、宣言をライブラリに追加した結果に関する問題を検出するのに使われます。

これに対して、[`linter.style.multiGoal`](#{root}/Option/MultiGoal.md) や [`linter.flexible`](#{root}/Option/Flexible.md) のようにソースコードの書き方をその場で警告するものは syntax linter です。
syntax linter は `#lint` ではなく、`set_option` などで有効化して使います。
[`Lean.Elab.Command.Linter`](#{root}/Type/Linter.md) は、この syntax linter を自作するための仕組みです。

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
