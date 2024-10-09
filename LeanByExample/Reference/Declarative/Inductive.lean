/- # inductive
`inductive` コマンドは、帰納型(inductive type)を定義することができます。

帰納型とは、有限個のコンストラクタで構成され、すべての項がいずれかのコンストラクタで構成されることが保証されているような型のことです。

## 帰納型の例

### 列挙型

帰納型の最も基本的な例は、次のような列挙型です。列挙型とは、固定された値のどれかを取るような型です。
-/
namespace Inductive --#

/-- 真か偽のどちらかの値をとる型 -/
inductive Bool : Type where
  | true
  | false

#check (Bool.true : Bool)

/- 列挙型は、帰納型の中でもすべてのコンストラクタが引数を持たないような特別な場合といえます。-/

/- ### 再帰的なデータ構造

一般には、帰納型のコンストラクタは引数を持つことができます。コンストラクタの引数の型が定義しようとしているその帰納型自身であっても構いません。これにより、連結リストや二分木といった再帰的な構造を持つデータ型を定義することができます。-/

/-- 連結リスト -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

/-- 2分木 -/
inductive BinTree (α : Type) : Type where
  | empty : BinTree α
  | node (value : α) (left : BinTree α) (right : BinTree α) : BinTree α

/- ### 帰納型の族

ある添字集合 `Λ : Type` の各要素 `λ : Λ` に対して、型 `T λ : Sort u` を定義することができます。簡単な例として、偶数を表す帰納型の族があります。
-/

/-- 自然数 `n` が偶数であることを表す命題 -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ (n : Nat) : Even n → Even (n + 2)

/- これで帰納型の族 `{Even 0, Even 2, Even 4, …}` を定義したことになります。

`inductive` コマンドは「パラメータを持つ帰納型」と「帰納型の族」を区別するため、「自然数 `n` が偶数である」ということを表す型を定義しようとして次のように書いたとすると、エラーになることに注意してください。
-/

/--
error: inductive datatype parameter mismatch
  0
expected
  n
-/
#guard_msgs in
  inductive BadEven (n : Nat) : Prop where
    | zero : BadEven 0
    | succ (m : Nat) : BadEven m → BadEven (m + 2)

/- このようにコードを書くと「すべての `n : Nat` に対して、帰納型 `BadEven n` を構成する」という意味になり、`zero : BadEven 0` だけでなく `zero : BadEven 1` や `zero : BadEven 2` なども存在すると宣言したことになります。したがって、右辺には `BadEven 0` ではなく `BadEven n` が来なければならないというエラーが出ているわけです。
-/

/- ## Peano の公理と帰納型
帰納型を利用すると、「Peano の公理に基づく自然数の定義」のような帰納的な公理による定義を表現することができます。

Peano の公理とは、次のようなものです:
* `0` は自然数。
* 後者関数と呼ばれる関数 `succ : ℕ → ℕ` が存在する。
* 任意の自然数 `n` に対して `succ n ≠ 0` が成り立つ。
* `succ` 関数は単射。つまり2つの異なる自然数 `n` と `m` に対して `succ n ≠ succ m` が成り立つ。
* 数学的帰納法の原理が成り立つ。つまり、任意の述語 `P : ℕ → Prop` に対して `P 0` かつ `∀ n : ℕ, P n → P (succ n)` ならば `∀ n : ℕ, P n` が成り立つ。

これを `inductive` を使用して再現すると次のようになります。
-/

/-- Peano の公理によって定義された自然数 -/
inductive MyNat : Type where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

/- 一見すると、これは不完全なように見えます。ゼロが自然数であること、後者関数が存在することは明示的に表現されているのでわかりますが、他の条件が表現されているかどうかは一見して明らかではありません。しかし、実は他の条件も暗黙のうちに表現されています。

まず `0 = succ n` となる自然数 `n` がないことですが、一般に帰納型の異なるコンストラクタ同士の像は重ならないことが保証されています。`injection` タクティクで証明ができます。
-/

example (n : MyNat) : .succ n ≠ MyNat.zero := by
  intro h
  injection h

/- また後者関数の単射性については、帰納型のコンストラクタは常に単射であることが保証されていて、ここから従います。-/

example (n m : MyNat) : MyNat.succ n = MyNat.succ m → n = m := by
  intro h
  injection h

/- 数学的帰納法の原理については、帰納型を定義したときに自動で生成される `.rec` という関数が対応しています。-/

/--
info: recursor Inductive.MyNat.rec.{u} : {motive : MyNat → Sort u} →
  motive MyNat.zero → ((n : MyNat) → motive n → motive n.succ) → (t : MyNat) → motive t
-/
#guard_msgs in #print MyNat.rec

end Inductive --#
