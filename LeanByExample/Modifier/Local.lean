/- # local
`local` はコマンドをその[セクション](#{root}/Declarative/Section.md)の内部でだけ有効にするための修飾子です。
-/
import Lean --#
section foo
  -- local を付けて新しい記法を定義
  local notation " succ' " => Nat.succ

  -- section の中では使用できる
  #check succ'
end foo

-- section を抜けると使えなくなる
#check_failure succ'

section foo
  -- 同じ名前の section を再度開いても使えない
  #check_failure succ'
end foo

/- コマンドの有効範囲を [`namespace`](#{root}/Declarative/Namespace.md) の内部に限定するのにも使えます。ただし、下記のコードで示しているように、`local` で修飾したコマンドの効果は同じ名前空間の中で永続するのではなく、`end` でその名前空間が閉じられたときに消失します。-/

namespace hoge
  -- local を付けて新しい記法を定義
  local notation " succ' " => Nat.succ

  -- 定義した namespace の中では使用できる
  #check succ' 2
end hoge

-- namespace の外では使用できない
#check_failure succ' 2

-- 再び同じ名前の namespace をオープンする
namespace hoge
  -- 使用できない！
  #check_failure succ'
end hoge

/- ## 修飾可能なコマンド
`local` で有効範囲を限定できるコマンドには、次のようなものがあります。
* [`elab`](#{root}/Declarative/Elab.md), `elab_rules`
* [`infix`](#{root}/Declarative/Infix.md), [`infixl`](#{root}/Declarative/Infixl.md), [`infixr`](#{root}/Declarative/Infixr.md)
* [`macro`](#{root}/Declarative/Macro.md), [`macro_rules`](#{root}/Declarative/MacroRules.md)
* [`notation`](#{root}/Declarative/Notation.md)
* [`postfix`](#{root}/Declarative/Postfix.md)
* [`prefix`](#{root}/Declarative/Prefix.md)
* [`instance`](#{root}/Declarative/Instance.md)
* [`syntax`](#{root}/Declarative/Syntax.md)
* などなど

リストの全体は、`local` の後に修飾できないコマンドを続けたときのエラーメッセージで確認できます。
-/

open Lean Parser in

/-- `s : String` をパースして `Syntax` の項を得る。`cat` は構文カテゴリ。-/
def parse (cat : Name) (s : String) : MetaM Syntax := do
  ofExcept <| runParserCategory (← getEnv) cat s

-- `def` は有効範囲を制限できないのでエラーになる
/-⋆-//--
error: <input>:1:6: expected 'binder_predicate', 'builtin_dsimproc', 'builtin_simproc', 'dsimproc',
'elab', 'elab_rules', 'infix', 'infixl', 'infixr', 'instance', 'macro', 'macro_rules',
'notation', 'postfix', 'prefix', 'simproc', 'syntax' or 'unif_hint'
-/
#guard_msgs in --#
#eval parse `command "local def"

/-
数が多いためすべての例を挙げることはしませんが、いくつか紹介します。たとえば `instance` の場合、`local` を付けて登録したインスタンスがその[セクション](#{root}/Declarative/Section.md)の内部限定になります。
-/

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

section
  -- local を付けてインスタンスを定義
  local instance : OfNat MyNat 0 where
    ofNat := MyNat.zero

  -- その section の中では使用できる
  #check (0 : MyNat)
end

-- section を抜けると使えなくなる
#check_failure (0 : MyNat)

/- ## 属性に対する local
属性付与の効果範囲を限定するためには、[`attribute`](#{root}/Declarative/Attribute.md) コマンドを `local` で修飾するのではなく、`attribute` コマンドの中で `local` を使います。
-/

def MyNat.add (n m : MyNat) : MyNat :=
  match m with
  | zero => n
  | succ m => succ (MyNat.add n m)

theorem MyNat.zero_add (n : MyNat) : MyNat.add .zero n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [MyNat.add, ih]

section
  -- [simp] 属性をローカルに付与する
  attribute [local simp] MyNat.zero_add

  -- その section の中では使用できる
  #check (by simp : MyNat.add .zero .zero = .zero)
end

-- section を抜けると simp 補題が利用できなくなる
#check_failure (by simp : MyNat.add .zero .zero = .zero)

/- ## 構文的な性質
[`local`](./Local.md) と [`scoped`](./Scoped.md) はともに構文的には `attrKind` に相当します。
-/

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name ← liftCoreM do realizeGlobalConstNoOverload x
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
