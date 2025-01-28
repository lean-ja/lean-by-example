/- # intro

`intro` は数学で慣習的に行われる

* `P → Q` を示すときに最初に `P` を仮定する
* `∀ x ∈ A, P(x)` を示すときに最初に `x ∈ A` が与えられたと仮定する

といった導入(introduction)を行います。

具体的には、`intro` は次のような挙動をします。

* ゴールが `⊢ P → Q` という形であるときに `P` をローカルコンテキストに追加して、ゴールを `⊢ Q` に変える。
* ゴールが `⊢ ∀ x, P x` という形であるときに `x` をローカルコンテキストに追加してゴールを `⊢ P x` に変える。
-/
variable (P Q R : Prop)

example (hPQ: P → Q) (hQR: Q → R) : P → R := by
  -- 示したいことが `P → R` なので、`P` だと仮定する
  intro hP

  -- 仮定 `hPQ : P → Q` と `hP : P` から `Q` が導かれる
  have hQ : Q := hPQ hP

  -- 仮定 `hQR : Q → R` と `hQ : Q` から `R` が導かれる
  exact hQR hQ

/- ## 特定の形の命題に対しての使用法

### A ∧ B → C
前提が論理積の形をしていた場合、[無名コンストラクタ](#{root}/Declarative/Structure.md#AnonymousConstructor)で仮定を分解することができます。
-/

example {S : Prop} (hPR : P → R) (hQR : Q → S) : P ∧ Q → R ∧ S := by
  -- `P ∧ Q` だと仮定する
  intro ⟨hP, hQ⟩

  constructor
  . exact hPR hP
  . exact hQR hQ

/- ### A ∨ B → C
前提が論理和の形をしていた場合、次のように分解することができます。-/

example (hPR : P → R) (hQR : Q → R) : P ∨ Q → R := by
  intro

  -- `P` が成り立つとする
  | Or.inl hP =>
    exact hPR hP

  -- `Q` が成り立つとする
  | Or.inr hQ =>
    exact hQR hQ

/- [`rcases`](./Rcases.md) を使って分解することも一般的です。-/

example (hPR : P → R) (hQR : Q → R) : P ∨ Q → R := by
  intro h
  rcases h with hP | hQ

  -- `P` が成り立つとする
  case inl =>
    exact hPR hP

  -- `Q` が成り立つとする
  case inr =>
    exact hQR hQ

/- また、`rintro` を使うと上記の `intro` と `rcases` の組み合わせを同時に行うことができます。-/

example (hPR : P → R) (hQR : Q → R) : P ∨ Q → R := by
  rintro (hP | hQ)

  -- `P` が成り立つとする
  case inl =>
    exact hPR hP

  -- `Q` が成り立つとする
  case inr =>
    exact hQR hQ

/- ### ∀ x, P x
`intro` は `∀ x, P x` という形のゴールにも使用できます。-/

example (P Q : Nat → Prop) (h : ∀ n, P n ↔ Q n) : ∀ y, P (y + 1) → Q (y + 1) := by
  -- 任意の `y` について示すので、`intro` で `y` を導入する
  -- そして `P (y + 1) → Q(y + 1)` を示したいので、`P (y + 1)` を仮定する
  intro y hyP

  -- `Q (y + 1)` を示せば良い
  show Q (y + 1)

  -- 同値を使ってゴールを書き換える
  rw [← h]

  -- 仮定 `P (y + 1)` より従う
  assumption

/- ## 否定 ¬ について

Lean では否定 `¬ P` は `P → False` として定義されているので、ゴールが `¬ P` のときに `intro` すると `P` が仮定に追加されて、ゴールが `False` に変わります。

`False` は矛盾を導けば証明できます。 -/

example (h: P → Q) : ¬Q → ¬P := by
  -- 示したいことが `¬Q → ¬P` なので、`¬Q` だと仮定する
  -- そうするとゴールが `¬P` になるので、
  -- さらに `intro` を行って仮定 `hP : P` を導入する
  intro hnQ hP

  -- 矛盾を示したい
  show False

  -- `hP : P` と `h : P → Q` から `Q` が導かれる
  have hQ : Q := h hP

  -- `hQ : Q` と `hnQ : ¬Q` から矛盾が導かれる
  contradiction

/-
## 関数の構成

より一般的には、`intro` は関数の構成に使うことができます。
`intro` が全称命題 `∀ x, P x` や含意 `P → Q` を統一的に扱うことができるのも、これらが Lean 内部で関数として扱われているからです。
-/
namespace Intro --#

variable {α : Type}

/-- `intro` による恒等関数の構成 -/
def f : α → α := by
  intro x
  exact x

example (x : α) : f x = id x := by dsimp [f]

end Intro --#
