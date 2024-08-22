/- # Cantor の定理

Cantor の定理とは、次のような定理です。

```admonish info title=""
どんな集合 `A` に対しても `A` より `A` のベキ集合 `𝒫 A` の方が真に濃度が大きくなります。

ただしここで「真に濃度が大きい」とは、

1. `A` から `𝒫 A` への全射が存在しない
1. `𝒫 A` から `A` への単射が存在しない

ということを意味しています。
```

この定理はもちろん Mathlib には既に存在しますが、ここでは Lean を用いて数学理論を形式化するとはどういうことかお見せするために、Mathlib を一切使わずに形式化していきます。
-/

/- ## 集合論の形式化

### 全体集合を固定する

まず、集合の概念を Lean で表現する必要があります。

Lean の型 `T : Type` は直観的には「項の集まり」を意味するので、これをそのまま集合だと考えてしまって、`t : T` をもって `t ∈ T` であると見なせばよいように思えるかもしれません。しかし Lean の型システムの性質上、この解釈は途中で破綻します。

たとえば `S T : Type` に対して共通部分の `S ∩ T` の要素は `S` にも `T` にも属していなくてはいけませんが、これは型の一意性から実現できません。`S ∪ T` についても同様で、`S` にも `S ∪ T` にも属している要素に正しく型をつけることができません。

そこで全体集合 `α : Type` を固定して、その中に含まれる集まりだけを考えることにします。
-/

/-- α を全体集合として、その部分集合の全体。
α の部分集合と α 上の述語を同一視していることに注意。 -/
def Set (α : Type) := α → Prop

variable {α : Type}

/-- `a : α` は集合 `s` に属する。数学では普通 `a ∈ s` と書かれる。 -/
def Set.mem (a : α) (s : Set α) : Prop := s a

/-- `s a` を `a ∈ s` と書けるようにする。 -/
instance : Membership α (Set α) := ⟨Set.mem⟩

/-- `A B : Set α` に対する共通部分 -/
def Set.inter (A B : Set α) : Set α := fun x => x ∈ A ∧ x ∈ B

/-- `A B : Set α` に対する合併 -/
def Set.union (A B : Set α) : Set α := fun x => x ∈ A ∨ x ∈ B

/- このようにしておくと、上記の問題は回避することができ、`S T : Set α` の共通部分や合併をとることができます。

### 内包記法の定義

「述語と部分集合を同一視する」という表現の良くないところは、集合を関数として扱うことになるので表記がわかりにくくなり、混乱を招きかねないということです。述語 `p : α → Prop` に対して内包記法 `{ x : α | p x}` が使用できるようにしましょう。

Lean のメタプログラミングフレームワークの力を借りれれば、そうしたことも可能です。
-/
section --#

variable {α : Type}

/-- 述語 `p : α → Prop` に対応する集合 -/
def setOf {α : Type} (p : α → Prop) : Set α := p

/-- 内包表記 `{ x : α | p x }` の `x : α` の部分のための構文。
`: α` の部分はあってもなくてもよいので `( )?` で囲っている。-/
syntax extBinder := ident (" : " term)?

/-- 内包表記 `{ x : α | p x }` の `{ | }` の部分のための構文。 -/
syntax (name := setBuilder) "{" extBinder " | " term "}" : term

/-- 内包表記の意味をマクロとして定義する -/
macro_rules
  | `({ $x:ident : $type | $p }) => `(setOf (fun ($x : $type) => $p))
  | `({ $x:ident | $p }) => `(setOf (fun ($x : _) => $p))

-- 内包表記が使えるようになったが、コマンドの出力や infoview では
-- いま定義した記法が使われないという問題がある
/-- info: setOf fun n => ∃ m, n = 2 * m : Set Nat -/
#guard_msgs in
  #check {n : Nat | ∃ m, n = 2 * m}

/-- infoview やコマンドの出力でも内包表記を使用するようにする -/
@[app_unexpander setOf]
def setOf.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $p) => `({ $x:ident | $p })
  | `($_ fun ($x:ident : $ty:term) => $p) => `({ $x:ident : $ty:term | $p })
  | _ => throw ()

-- 正常に動作することを確認

/-- info: {n | ∃ m, n = 2 * m} : Set Nat -/
#guard_msgs in
  #check {n | ∃ m, n = 2 * m}

/-- info: {n | ∃ m, n = 2 * m} : Set Nat -/
#guard_msgs in
  #check {n : Nat | ∃ m, n = 2 * m}

end --#

/- ### 全射と単射
関数 `f : A → B` が全射であるとは、任意の `b : B` に対して `f a = b` となる `a : A` が存在することです。また、`f` が単射であるとは、任意の `a₁, a₂ : A` に対して `f a₁ = f a₂` ならば `a₁ = a₂` となることです。

これを Lean で表現すると次のようになります。
-/
section --#

variable {α β : Type}

/-- 関数の全射性 -/
def Function.surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b

/-- 関数の単射性 -/
def Function.injective (f : α → β) : Prop := ∀ {a₁ a₂ : α}, f a₁ = f a₂ → a₁ = a₂

end --#
/-
```admonish warning title="注意"
上記の定義を見て、関数の定義域と値域が `A B : Set α` ではなくて `α β : Type` であることに違和感を感じられたかもしれません。型と集合は異なると上で書いたばかりなのに、なぜここでは型を使っているのでしょうか？

実際に `A B : Set α` に対して関数の集合 `Hom A B` を定義しようとすると、その理由がわかるかもしれません。

`f ∈ Hom A B` が持つべき性質として `a ∈ A → f a ∈ B` があります。`A : Set α` と `B : Set α` をそれぞれ部分型 `{ a : α // a ∈ A }`, `{b : α // b ∈ B}` と同一視すれば、`Hom A B` は関数型 `{ a : α // a ∈ A } → { b : α // b ∈ B }` になります。

結局関数型を考えていることになるので、`α β : Type` について考えれば十分だということになるわけです。
```
-/

/- ## 問題
以上の準備のもとで、Cantor の定理を証明することができます。次の `sorry` の部分を埋めてください。
-/
section --#

variable {α : Type}

open Function

/-- ある集合からそのベキ集合への全射は存在しない -/
theorem cantor_surjective (f : α → Set α) : ¬ surjective f := by
  -- `f` が全射であると仮定する
  intro hsurj

  -- `α` の部分集合 `A : Set α` を「像が自分自身を含まない要素全体」とする --##
  let A : Set α := /- sorry -/ {a | a ∉ f a}

  -- `f` は全射なので、ある `a` が存在して `f a = A`
  obtain ⟨a, ha⟩ := hsurj A

  -- `a ∈ A` は `a ∉ A` と同値である
  have : a ∈ A ↔ a ∉ A := by
    -- sorry
    -- `f a = A` なので `a ∉ A` は `a ∉ f a` と同値
    rw [show (a ∉ A) = (a ∉ f a) from by rw [ha]]

    -- `A` の定義から `a ∈ A` は `a ∉ f a` と同値
    rw [show (a ∈ A) ↔ (a ∉ f a) from by rfl]
    -- sorry

  -- これは矛盾
  simp at this

/-- ベキ集合から元の集合への単射は存在しない -/
theorem cantor_injective (f : Set α → α) : ¬ injective f := by
  -- `f` が単射だと仮定する
  intro hinj

  -- `α` の部分集合 `A : Set α` を「fによる逆元に含まれないようなfの像全体」とする --##
  let A : Set α := /- sorry -/{a | ∃ B : Set α, a = f B ∧ f B ∉ B}

  -- このとき `f A ∈ A` と `f A ∉ A` が同値になる
  have : (f A ∈ A) ↔ (f A ∉ A) := by
    -- sorry
    constructor

    -- 左から右を示す
    case mp =>
      -- `f A ∈ A` と仮定する
      intro hmem
      exfalso

      -- `f A ∈ A` なので `A` の定義から、
      -- ある `B : Set α` が存在して `f A = f B` かつ `f B ∉ B`
      have ⟨B, hf, hB⟩ := hmem

      -- `f` は単射なので `A = B` である
      have hAB : A = B := hinj hf

      -- これは `f A ∉ A` を意味し、矛盾
      rw [← hAB] at hB
      contradiction

    -- 右から左を示す
    case mpr =>
      -- `f A ∉ A` と仮定する
      intro hmem

      -- `A` の定義により、これはまさに `f A ∈ A` を意味する
      -- よって矛盾
      exact ⟨A, rfl, hmem⟩
    -- sorry

  -- これは矛盾である
  simp at this
end --#
