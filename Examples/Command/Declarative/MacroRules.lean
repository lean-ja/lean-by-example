/- # macro_rules
`macro_rules` はマクロ展開を定めるためのコマンドです。

[`macro`](./Macro.md) コマンドと似ていますが、以下のように `macro_rules` の方がより低水準で汎用的なコマンドです。

* `macro` コマンドは構文の宣言を同時に行いますが、`macro_rules` は構文宣言は行いません。
* `macro` コマンドは展開ルールを一つ追加しますが、`macro_rules` は複数の展開ルールを一度に定義できます。
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

/- `macro_rules` コマンドは上記の例のように、`=>` 記号を境に分かれており、左辺の構文要素を右辺の構文に変換するというルールを定義します。-/

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
`macro_rules` の右辺に自分自身を含めることができます。これにより、再帰的なマクロ展開を定義することができます。
-/

-- 再帰的なマクロ展開を定義。
-- `P` と `Q` が両方 `my_trivial` で示せるなら、
-- `P ∧ Q` が `my_trivial` で示せるようになる。
macro_rules
  | `(tactic| my_trivial) => `(tactic| apply And.intro <;> my_trivial)

example {α : Type} {P : Prop}(x : α) (h : P) : x = x ∧ P := by
  my_trivial
