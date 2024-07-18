/- # inductive
`inductive` コマンドは、帰納型(inductive type)を定義することができます。Lean でユーザが新しい型を定義する主要な方法です。

## 帰納型の例
帰納型の最も基本的な例は、次のような列挙型です。列挙型とは、固定された値のどれかを取るような型です。
-/
namespace Inductive --#

/-- 真か偽のどちらかの値をとる型 -/
inductive Bool : Type where
  | true
  | false

#check (Bool.true : Bool)

/- 列挙型は、帰納型の中でもすべてのコンストラクタが引数を持たないような特別な場合といえます。一般には、帰納型のコンストラクタは引数を持つことができます。-/
universe u v

/-- `α` と `β` の直和型 -/
inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β

/- コンストラクタの引数の型が定義しようとしているその帰納型自身であっても構いません。 -/

/-- 連結リスト -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

/- ## Peano の公理と帰納型
帰納型を利用すると、「Peano の公理に基づく自然数の定義」のような帰納的な公理による定義を表現することができます。

Peano の公理とは、次のようなものです:
* `0` は自然数.
* 後者関数と呼ばれる関数 `succ : ℕ → ℕ` が存在する。
* 任意の自然数 `n` に対して `succ n ≠ 0`.
* `succ` 関数は単射。つまり2つの異なる自然数 `n` と `m` に対して `succ n ≠ succ m`.
* 数学的帰納法の原理が成り立つ。つまり、任意の述語 `P : ℕ → Prop` に対して `P 0` かつ `∀ n : ℕ, P n → P (succ n)` ならば `∀ n : ℕ, P n`.

これを `inductive` を使用して再現すると次のようになります。
-/

/-- Peano の公理によって定義された自然数 -/
inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

/- 一見すると、これは不完全なように見えます。ゼロが自然数であること、後者関数が存在することは明示的に表現されているのでわかりますが、他の条件が表現されているかどうかは一見して明らかではありません。しかし、実は他の条件も暗黙のうちに表現されています。

まず `0 = succ n` となる自然数 `n` がないことですが、一般に帰納型の異なるコンストラクタ同士の像は重ならないことが保証されています。`injection` タクティクで証明ができます。
-/

example (n : Nat) : .succ n ≠ Nat.zero := by
  intro h
  injection h

/- また後者関数の単射性については、帰納型のコンストラクタは常に単射であることが保証されていて、ここから従います。-/

example (n m : Nat) : Nat.succ n = Nat.succ m → n = m := by
  intro h
  injection h

/- 数学的帰納法の原理については、帰納型を定義したときに自動で生成される `.rec` という関数が対応しています。-/

/--
info: recursor Inductive.Nat.rec.{u} : {motive : Nat → Sort u} →
  motive Nat.zero → ((n : Nat) → motive n → motive n.succ) → (t : Nat) → motive t
-/
#guard_msgs in #print Nat.rec

end Inductive --#
