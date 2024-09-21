/- # declare_syntax_cat

[`🏷️メタプログラミング`](./?search=🏷メタプログラミング)

`declare_syntax_cat` コマンドは、新しい構文カテゴリを宣言するためのコマンドです。構文カテゴリを宣言することで、宣言した構文を再利用可能にして冗長な構文宣言を減らすことができます。

例として、集合の内包表記 `{x : T | P x}` を定義するコードを示します。
-/
namespace DeclareSyntaxCat --#

universe u

/-- `α` を全体集合とする部分集合の全体 -/
def Set (α : Type u) := α → Prop

variable {α : Type u}

/-- 項 `x : α` が `X : Set α` に属する -/
def Set.mem (X : Set α) (x : α) : Prop := X x

/-- `x ∈ X` と書けるようにする -/
instance : Membership α (Set α) where
  mem := Set.mem

/-- 述語 `p : α → Prop` から構成される集合 -/
def setOf (p : α → Prop) : Set α := p

/-- binder という構文カテゴリ。
これは変数束縛を表していて、
`{x : X | P x}` の `x : X` の部分とか
`{x ∈ X | P x}` の `x ∈ X` の部分とかを表している -/
declare_syntax_cat binder

/-- `{x : T | P x}` の `: T` の部分。
あってもなくて良いので `( )?` で囲う -/
syntax ident (" : " term)? : binder

/-- `{x ∈ T | P x}` の `∈ T` の部分。
あってもなくて良いので `( )?` で囲う -/
syntax ident (" ∈ " term)? : binder

/-- 集合の内包表記 -/
syntax "{" binder "|" term "}" : term

-- 合法な構文として認識される
-- 実装は与えていないのでエラーにはなる
#check_failure { x | x = 0}
#check_failure { x : Nat | x > 0 }
#check_failure { x ∈ T | x = 0}

/-- `{x : T | P x}` と `{x ∈ T | P x}` の形の式を `setOf` の式に変換する -/
macro_rules
  | `({ $var:ident | $body:term }) => `(setOf (fun $var => $body))
  | `({ $var:ident : $ty:term | $body:term }) => `(setOf (fun ($var : $ty) => $body))
  | `({ $var:ident ∈ $s:term | $body:term }) => `(setOf (fun $var => $var ∈ $s ∧ $body))

-- 内包表記が使えるようになった
#check { x : Nat | x > 0 }

#check
  let Even := { x : Nat | x % 2 = 0 }
  { x ∈ Even | x > 0 }

end DeclareSyntaxCat --#
