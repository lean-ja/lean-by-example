/- # scoped
`scoped` は、コマンドの有効範囲を現在の名前空間に限定します。
-/
import Lean --#
-- #target をコマンドとして認識させる
-- 実装は与えない
syntax "#greet" : command

namespace Scoped
  -- scoped を付けて greet コマンドをマクロとして定義
  scoped macro "#greet" : command => `(#eval "hello, world!")

  -- その名前空間の中では greet コマンドが利用できる
  #greet

end Scoped

-- 名前空間を抜けると使えなくなる
/-- error: elaboration function for '«command#greet»' has not been implemented -/
#guard_msgs in #greet

-- 再び同じ名前で名前空間を開く
namespace Scoped
    -- その名前空間の中では greet コマンドが利用できる
    #greet

end Scoped

section
  open Scoped

  -- 単に open するだけでも利用できるようになる
  #greet
end

/- `scoped` で有効範囲を限定できるコマンドには、次のようなものがあります。
* `elab`, `elab_rules`
* [`infix`](./Infix.md), `infixl`, `infixr`
* [`instance`](./Instance.md)
* [`macro`](./Macro.md), [`macro_rules`](./MacroRules.md)
* [`notation`](./Notation.md)
* [`postfix`](./Postfix.md)
* [`prefix`](./Prefix.md),
* `syntax`
* などなど

リストの全体は、`scoped` の後に修飾できないコマンドを続けたときのエラーメッセージで確認できます。
-/

open Lean Parser

/-- parse できるかどうかチェックする関数 -/
def checkParse (cat : Name) (s : String) : MetaM Unit := do
  if let .error s := runParserCategory (← getEnv) cat s then
    throwError s

-- `def` は有効範囲を制限できないのでエラーになる
/--
error: <input>:1:7: expected 'binder_predicate', 'builtin_dsimproc', 'builtin_simproc', 'dsimproc',
'elab', 'elab_rules', 'infix', 'infixl', 'infixr', 'instance',
'macro', 'macro_rules', 'notation', 'postfix', 'prefix', 'simproc',
'syntax' or 'unif_hint'
-/
#guard_msgs in
  run_meta checkParse `command "scoped def"

/- ## open scoped
`open scoped` コマンドを利用すると、特定の名前空間にある `scoped` が付けられた名前だけを有効にすることができます。単に [`open`](./Open.md) コマンドを利用するとその名前空間にあるすべての名前が有効になります。
-/

namespace Foo
  -- Foo の中でのみ有効な add' という名前を定義
  scoped infix:55 " add' " => Nat.add

  -- 動作する
  #guard 30 add' 12 = 42

  -- Foo の中で greet も定義
  def greet := "hello"

end Foo

section
  -- 単に open した場合、どちらも使用可能
  open Foo

  #check (30 add' 12)

  #check greet
end

section
  -- open scoped とした場合
  open scoped Foo

  -- scoped がついた宣言は使用可能
  #check (30 add' 12)

  -- greet は使えないまま
  #check_failure greet
end
