/- # 暗黙の引数

暗黙の引数とは、[`def`](#{root}/Declarative/Def.md) コマンドや [`theorem`](#{root}/Declarative/Theorem.md) コマンド、[`variable`](#{root}/Declarative/Variable.md) コマンドなどが受け取る構文の一つで、関数や定理の引数をユーザが明示的に与えなくても、Lean が文脈を読んで推論してくれるようになります。波括弧 `{}` で囲んで、`{x y : A}` のように書きます。

## 典型的な使用例

たとえば、暗黙の引数を使わなかった場合にどうなるかを見てみましょう。次の関数 `List.subs` は型パラメータ `α : Type` を受け取っていますが、第二引数 `xs : List α` を見れば `α : Type` が何であるかは分かるので、`List.subs` を使用する際に毎回 `α` を指定するのは冗長だと考えられます。
-/
import Lean --#

/-- 与えられたリストの部分リストを全て返す(明示的引数バージョン) -/
def List.subsₑ (α : Type) (xs : List α) : List (List α) :=
  match xs with
  | [] => [[]]
  | x :: xs =>
    let xss := subsₑ α xs
    xss ++ xss.map (x :: ·)

-- 型引数 α を明示的に与える必要がある
#eval List.subsₑ Nat [1, 2]

-- 型引数を与えないと（当然ながら）エラーになってしまう
#check_failure List.subs [1, 2]

/- 引数 `α` を暗黙の引数として受け取るように変更すれば、Lean が `α : Type` の内容を推論してくれるようになり、`α` を省略できるようになります。-/

/-- 与えられたリストの部分リストを全て返す(暗黙引数バージョン) -/
def List.subsᵢ {α : Type} (xs : List α) : List (List α) :=
  match xs with
  | [] => [[]]
  | x :: xs =>
    let xss := subsᵢ xs
    xss ++ xss.map (x :: ·)

-- 型引数を省略できるようになった
#eval List.subsᵢ [1, 2]

-- 逆に今度は型引数を与えるとエラーになる
#check_failure List.subsᵢ Nat [1, 2]

/- ## 明示引数モード

暗黙の引数を受け取るものとして定義された関数や定理に対して、`@` 記号を先頭に付けると全ての暗黙の引数が明示的引数に変化します。
-/

-- 2 つの暗黙引数を持つ関数
def List.map' {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map' f xs

-- 普通は次のように使う
#check List.map' (fun x => x == 1) [1, 2, 3]

-- `@` 記号を付けると全ての引数が明示的引数に変化
#check @List.map' Nat Bool (fun x => x == 1) [1, 2, 3]

/- ## 狭義の暗黙の引数

`⦃x⦄` のように二重の中括弧で書くと、狭義の暗黙の引数 (strict implicit argument) になります。
通常の暗黙引数 `{x}` とは違って、後続の明示引数が与えられるまで `_` を自動挿入しません。

TPiL の次のような単調性の定義は、この狭義の暗黙の引数を使った例です。
-/

/-- 単調性（狭義の暗黙引数を使った定義） -/
def Monotone (f : Int → Int) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

variable {α : Type} {s : Set α} {p : α → Prop} {y : α}

-- fully applied な形では、`{}` と `⦃⦄` は同じように使える
def strictImplicitExample (h : ∀ ⦃x : α⦄, x ∈ s → p x) (hs : y ∈ s) : p y :=
  h hs

def implicitExample (h : ∀ {x : α}, x ∈ s → p x) (hs : y ∈ s) : p y :=
  h hs

/- ## 構文的な性質

`Lean.Parser.Term.implicitBinder` は `{x}` 形式の暗黙引数を、`Lean.Parser.Term.strictImplicitBinder` は `⦃x⦄` 形式の狭義の暗黙引数を扱うパーサです。
それぞれのドキュメントコメントは次の通りです。

{{#include ./ImplicitBinder/Doc.md}}
{{#include ./ImplicitBinder/StrictDoc.md}}
-/

-- `x : α` と書いたので、`α` が何かの型であることは分かる
def myId {α} (x : α) := x
