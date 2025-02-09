/- # macro_rules

`macro_rules` は[マクロ](#{root}/Type/Macro.md)展開を定義するためのコマンドです。類似のコマンドに [`macro`](#{root}/Declarative/Macro.md) コマンドがあります。
-/

/-- `#hello` コマンドの構文の定義。
オプションの引数を受け取るようにしておく。 -/
syntax "#hello" (str)? : command

macro_rules
  | `(#hello) => `(command| #eval "Hello, Lean!")
  | `(#hello $name) => `(command| #eval s!"Hello, {$name}!")

/-⋆-//-- info: "Hello, Lean!" -/
#guard_msgs in --#
#hello

/-⋆-//-- info: "Hello, world!" -/
#guard_msgs in --#
#hello "world"

/- `macro_rules` コマンドは上記の例のように、`=>` 記号を境に分かれており、左辺の構文を右辺の構文に変換するというルールを定義します。 -/

/- ## 展開ルールの上書きと追加

一つの構文に対して `macro_rules` で複数の展開ルールを宣言することができます。このとき、最後に宣言されたルールから先に適用されます。
-/

/-- 挨拶するコマンド -/
syntax "#greet" : command

-- `#greet` という構文に2つの展開ルールを定義

macro_rules
  | `(command| #greet) => `(#eval "Hello, Lean!")

macro_rules
  | `(command| #greet) => `(#eval "Good morning, Lean!")

-- 最後に宣言されたルールが適用される
/-- info: "Good morning, Lean!" -/
#guard_msgs in #greet

/- このとき古い方の展開ルールは常に上書きされて消えるわけではありません。`macro_rules` で宣言されたルールは最後に宣言されたものから順に試され、展開に失敗するとスキップされ、最初に展開に成功したルールが採用されます。具体例でこの挙動を確認してみましょう。
-/

/-- `trivial` というタクティクの類似物 -/
syntax "my_trivial" : tactic

-- `assumption` タクティクを呼び出す
macro_rules
  | `(tactic| my_trivial) => `(tactic| assumption)

-- `rfl` タクティクを呼び出す
macro_rules
  | `(tactic| my_trivial) => `(tactic| rfl)

-- 後から追加されたルールが先に適用されるので、Lean はまず `rfl` に展開しようとする。
-- しかし `rfl` はゴールの形が不適切なので失敗する。
-- その後 `assumption` が試され、それは通る。
example (P : Prop) (h : P) : P := by
  my_trivial

-- `rfl` が使われて通る
example {α : Type} (x : α) : x = x := by
  my_trivial

/- ## 再帰的展開
`macro_rules` の右辺に、これから解釈しようとしている構文自身を含めることができます。これにより、再帰的なマクロ展開を定義することができます。
-/

example {α : Type} {P : Prop} (x : α) (h : P) : x = x ∧ P := by
  -- 最初は示せない
  fail_if_success my_trivial

  -- 手動で示す
  apply And.intro
  · rfl
  · assumption

-- 再帰的なマクロ展開を定義。
-- `P` と `Q` が両方 `my_trivial` で示せるなら、
-- `P ∧ Q` が `my_trivial` で示せるようになる。
macro_rules
  | `(tactic| my_trivial) => `(tactic| apply And.intro <;> my_trivial)

example {α : Type} {P : Prop} (x : α) (h : P) : x = x ∧ P := by
  -- `my_trivial` で示せるようになった！
  my_trivial

/- ## 使用例

`macro_rules` を理解する一番の近道は、具体例をたくさん見ることです。以下に、`macro_rules` のシンプルな使用例をいくつか紹介します。

### 集合の波括弧記法

`macro_rules` を使用して、集合の波括弧記法 `{{ a₁, a₂, ..., aₙ }}` を解釈するマクロを定義する例を以下に示します。
-/

/-- 部分集合。`α` の部分集合 `A ⊆ α` は、任意の要素 `x : α` に対して
それが `A` の要素かどうか判定する述語 `A : α → Prop` と同一視できる。-/
def Set (α : Type) := α → Prop

namespace Set

  variable {α : Type}

  /-- 1つの要素だけからなる集合 -/
  def singleton (a : α) : Set α := fun x => x = a

  /-- 集合に１つ要素を追加する -/
  def insert (a : α) (s : Set α) := fun x => x = a ∨ s x

end Set

-- 集合の波括弧記法の定義。
-- 既存の記号と被らないようにするために二重にしている。
-- なお `term,*` は `term` が `,` 区切りで0個以上続く列を表す。
syntax "{{" term,* "}}" : term

-- `syntax` コマンドは記法の解釈方法を決めていないので、エラーになる
#check_failure {{2, 3}}

-- 集合の波括弧記法をどう解釈するかのルールを定める
macro_rules
  | `(term| {{$x}}) => `(Set.singleton $x)
  | `(term| {{$x, $xs:term,*}}) => `(Set.insert $x {{$xs,*}})

-- 集合の波括弧記法が使えるようになった
#check ({{2, 3, 4, 5}} : Set Nat)

/- ### 入れ子リスト

Lean 標準の `List : Type → Type` はリストの要素が同じ型であることを要求しており、「リストのリスト」にリストではない要素を混入させることを許しませんが、それを許すような入れ子リストを定義して、そのための構文を用意する例を示しましょう。[^nestedlist]
-/

/-- 入れ子になったリスト -/
inductive NestedList (α : Type) : Type
  /-- 空リスト -/
  | nil : NestedList α
  /-- NestedList に要素を追加する -/
  | conse : α → NestedList α → NestedList α
  /-- NestedList に NestedList を追加する -/
  | consl : NestedList α → NestedList α → NestedList α
deriving DecidableEq

namespace NestedList
  /- ## NestedList を定義する構文を作る -/

  /-- NestedList を定義するための構文。 -/
  syntax "《" term,* "》" : term

  -- `syntax` コマンドは記法の解釈方法を決めていないので、エラーになる
  #check_failure 《1, 《2, 3》, 4》

  macro_rules
    | `(《》) => `(NestedList.nil)
    | `(《《$xs,*》》) => `(NestedList.consl 《$xs,*》 NestedList.nil)
    | `(《《$xs,*》, $ys,*》) => `(NestedList.consl 《$xs,*》 《$ys,*》)
    | `(《$x》) => `(NestedList.conse $x NestedList.nil)
    | `(《$x, $xs,*》) => `(NestedList.conse $x 《$xs,*》)

  -- NestedList を見やすく定義できるようになった！
  #check 《1, 《2, 3》, 4》

  #guard
    let xs := 《1, 2》
    let ys := NestedList.conse 1 <| .conse 2 NestedList.nil

    -- 両者は同じものを表している！
    xs = ys

end NestedList
/- ### リスト内包表記

マクロとして **リスト内包表記(list comprehension)** を導入する例を以下に示します。[^listcompr]
-/
namespace ListComp
  /- # リスト内包表記 -/

  /-- リスト内包表記 -/
  declare_syntax_cat compClause

  syntax "for " term " in " term : compClause
  syntax "if " term : compClause
  syntax "[" term " | " compClause,* "]" : term

  -- `syntax` コマンドは記法の解釈方法を決めていないので、エラーになる
  #check_failure [x | for x in [1, 2, 3, 4, 5]]
  #check_failure [x | if x < 2]
  #check_failure [x | for x in [1, 2, 3], if x < 2]

  macro_rules
    | `([$t |]) => `([$t])
    | `([$t | for $x in $xs]) => `(List.map (fun $x => $t) $xs)
    | `([$t | if $x]) => `(if $x then [$t] else [])
    | `([$t | $c, $cs,*]) => `(List.flatten [[$t | $cs,*] | $c])

  -- for 構文のテスト
  #guard [x ^ 2 | for x in [1, 2, 3, 4, 5]] = [1, 4, 9, 16, 25]

  -- ２重の for 構文のテスト
  #guard
    let lhs := [(x, y) | for x in [1, 2, 3], for y in [4, 5]]
    let rhs := [(1, 4), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5)]
    lhs = rhs

  -- if 構文のテスト
  #guard [x | for x in [1, 2, 3], if x < 2] = [1]

end ListComp
/- ### 数式を Lean に埋め込む

`1 + 2 * 3` のような数式（値ではなくて式そのもの）を Lean の式として解釈するマクロを以下に示します。
-/

/-- 2項演算の集合 -/
inductive Op where
  /-- 加法 -/
  | add
  /-- 乗法 -/
  | mul
deriving DecidableEq

/-- 数式 -/
inductive Expr where
  /-- 数値リテラル -/
  | val : Nat → Expr
  /-- 演算子の適用 -/
  | app : Op → Expr → Expr → Expr
deriving DecidableEq

namespace Expr
  /- ## Expr の項を定義するための簡単な構文を用意する -/

  /-- `Expr` のための構文カテゴリ -/
  declare_syntax_cat expr

  /-- `Expr` を見やすく定義するための構文 -/
  syntax "expr!{" expr "}" : term

  -- 数値リテラルは数式
  syntax:max num : expr

  -- 数式を `+` または `*` で結合したものは数式
  -- `+` と `*` のパース優先順位を指定しておく
  syntax:30 expr:30 " + " expr:31 : expr
  syntax:35 expr:35 " * " expr:36 : expr

  -- 数式を括弧でくくったものは数式
  syntax:max "(" expr ")" : expr

  -- `syntax` コマンドは記法の解釈方法を決めていないので、エラーになる
  #check_failure expr!{1 + 2}
  #check_failure expr!{1 * 2}
  #check_failure expr!{(1 + 2) * 3}

  macro_rules
    | `(expr!{$n:num}) => `(Expr.val $n)
    | `(expr!{$l:expr + $r:expr}) => `(Expr.app Op.add expr!{$l} expr!{$r})
    | `(expr!{$l:expr * $r:expr}) => `(Expr.app Op.mul expr!{$l} expr!{$r})
    | `(expr!{($e:expr)}) => `(expr!{$e})

  -- 足し算は左結合になる
  #guard
    let expected := app Op.add (app Op.add (val 1) (val 2)) (val 3)
    let actual := expr!{1 + 2 + 3}
    actual = expected

  -- 掛け算は左結合になる
  #guard
    let expected := app Op.mul (app Op.mul (val 1) (val 2)) (val 3)
    let actual := expr!{1 * 2 * 3}
    actual = expected

  -- 足し算と掛け算が混在する場合は、掛け算が優先される
  #guard
    let expected := app Op.add (app Op.mul (val 1) (val 2)) (val 3)
    let actual := expr!{1 * 2 + 3}
    actual = expected

end Expr

/- [^nestedlist]: ここで紹介しているコード例は、Lean 公式 Zulip の "macro parser for nested lists" というトピックで [Kyle Miller さんが挙げていたコード](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/macro.20parser.20for.20nested.20lists/near/486691429)を参考にしています。
[^listcompr]: ここで紹介しているコード例は、Lean 公式 Zulip の "List Functor" というトピックで [Kyle Miller さんが挙げていたコード](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/List.20Functor/near/290456697)を参考にしています。
-/
