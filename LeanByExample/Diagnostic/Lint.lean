/- # \#lint

`#lint` コマンドは、環境リンター(environment linter)を実行します。

環境リンターとは何かというと、Lean のリンター（よくない書き方のコードを検出するツール）の分類名です。
Lean のリンターには次の２種類があります。

* 環境リンター(environment linter): 環境に登録された定義・定理・インスタンスなどを検査するリンター。
  [`#lint`](#{root}/Diagnostic/Lint.md) コマンドや `lake lint` コマンドで実行することができる。
* 構文リンター(syntax linter): ソースコードの構文を見て、良くない書き方をその場で警告するリンター。
  `set_option` コマンドなどで有効化して使う。
  [`Lean.Elab.Command.Linter`](#{root}/Type/Linter.md) を構成することによって自作できる。

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
