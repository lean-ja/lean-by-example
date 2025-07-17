/- # scoped
`scoped` は、コマンドの有効範囲を現在の名前空間に限定します。
-/
import Lean --#
-- #greet をコマンドとして認識させる
-- 実装は与えない
syntax "#greet" : command

namespace Scoped
  -- scoped を付けて greet コマンドをマクロとして定義
  scoped macro "#greet" : command => `(#eval "hello, world!")

  -- その名前空間の中では greet コマンドが利用できる
  #greet

end Scoped

-- 名前空間を抜けると使えなくなる
/-⋆-//-- error: elaboration function for '«command#greet»' has not been implemented -/
#guard_msgs in --#
#greet

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

/- ## 修飾可能なコマンド
`scoped` で有効範囲を限定できるコマンドには、次のようなものがあります。
* [`elab`](#{root}/Declarative/Elab.md), `elab_rules`
* [`infix`](#{root}/Declarative/Infix.md), [`infixl`](#{root}/Declarative/Infixl.md), [`infixr`](#{root}/Declarative/Infixr.md)
* [`instance`](#{root}/Declarative/Instance.md)
* [`macro`](#{root}/Declarative/Macro.md), [`macro_rules`](#{root}/Declarative/MacroRules.md)
* [`notation`](#{root}/Declarative/Notation.md)
* [`postfix`](#{root}/Declarative/Postfix.md)
* [`prefix`](#{root}/Declarative/Prefix.md),
* [`syntax`](#{root}/Declarative/Syntax.md)
* などなど

リストの全体は、`scoped` の後に修飾できないコマンドを続けたときのエラーメッセージで確認できます。
-/

open Lean Parser

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

-- `def` は有効範囲を制限できないのでエラーになる
/-⋆-//--
error: <input>:1:7: expected 'binder_predicate', 'builtin_dsimproc', 'builtin_simproc', 'dsimproc',
'elab', 'elab_rules', 'infix', 'infixl', 'infixr', 'instance',
'macro', 'macro_rules', 'notation', 'postfix', 'prefix', 'simproc',
'syntax' or 'unif_hint'
-/
#guard_msgs in --#
#eval parse `command "scoped def"

/- ## open scoped
`open scoped` コマンドを利用すると、特定の名前空間にある `scoped` が付けられた名前だけを有効にすることができます。単に [`open`](#{root}/Declarative/Open.md) コマンドを利用するとその名前空間にあるすべての名前が有効になります。
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

/- ## 属性に対する scoped

`attribute` コマンドの中で `scoped` を使用すると、属性付与の効果範囲を限定することができます。
-/
namespace Bar

  @[scoped simp]
  def bar : Nat := 12

  example : bar = 12 := by
    simp

end Bar

example : Bar.bar = 12 := by
  -- `scoped`が付いているので、使えない
  fail_if_success simp

  dsimp [Bar.bar]

section
  -- 名前空間を開く
  open Bar

  example : bar = 12 := by
    -- 名前空間を開いたので、`simp`が使える
    simp

end
/- ## 構文的な性質
[`local`](./Local.md) と [`scoped`](./Scoped.md) はともに構文的には `attrKind` に相当します。
-/

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name := x.getId
  if let some s ← findDocString? (← getEnv) name then
    logInfo m!"{s}"

/-⋆-//--
info: `attrKind` matches `("scoped" <|> "local")?`, used before an attribute like `@[local simp]`.
-/
#guard_msgs in --#
#doc Lean.Parser.Term.attrKind

/-- 例示のための意味のないコマンド。直前に `attrKind` のみを受け付ける。-/
macro attrKind "#greet " : command => `(#eval "hello")

-- パース出来るので、`local` と `scoped` は同じカテゴリに属する
local #greet
scoped #greet
