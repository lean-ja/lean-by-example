/- # \#lint

`#lint` コマンドは、環境リンター(environment linter)を実行します。

環境リンターとは何かというと、Lean のリンター（よくない書き方のコードを検出するツール）の分類名です。
Lean のリンターには次の２種類があります。

* 環境リンター(environment linter): 環境に登録された定義・定理・インスタンスなどを検査するリンター。
  [`#lint`](#{root}/Diagnostic/Lint.md) コマンドや `lake lint` コマンドで実行することができる。
* 構文リンター(syntax linter): 各コマンドのエラボレーション（Lean がコードを処理するフェーズ）のたびに自動的に実行されるリンター。
  `set_option` コマンドで個別に有効化・無効化することができる。
  [`Lean.Elab.Command.Linter`](#{root}/Type/Linter.md) を構成することによって自作できる。

「構文リンター」という名前は、リンターが `Syntax` 型の値（コードの構文木）を入力として受け取ることに由来します。
ただし、チェックの内容が必ずしも「構文的」なものに限らず、環境に登録された情報（公理への依存関係など）を参照することもあります。
環境リンターとの違いは「チェックする内容」ではなく「実行タイミングと方法」にあります。

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
