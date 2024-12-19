/- # inductive
`inductive` コマンドは、帰納型(inductive type)を定義することができます。

帰納型とは、有限個のコンストラクタで構成され、すべての項がいずれかのコンストラクタで構成されることが保証されているような型のことです。

## 帰納型の例

### 列挙型

帰納型の最も基本的な例は、次のような列挙型です。列挙型とは、固定された値のどれかを取るような型です。
-/

/-- 真か偽のどちらかの値をとる型 -/
inductive MyBool : Type where
  | true
  | false

#check (MyBool.true : MyBool)

/- 列挙型は、帰納型の中でもすべてのコンストラクタが引数を持たないような特別な場合といえます。-/

/- ### 再帰的なデータ構造

一般には、帰納型のコンストラクタは引数を持つことができます。コンストラクタの引数の型が定義しようとしているその帰納型自身であっても構いません。これにより、連結リストや二分木といった再帰的な構造を持つデータ型を定義することができます。-/
namespace Hidden --#

/-- 連結リスト -/
inductive List (α : Type) : Type where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

end Hidden --#
/-- 2分木 -/
inductive BinTree (α : Type) : Type where
  | empty : BinTree α
  | node (value : α) (left right : BinTree α) : BinTree α

/- ### 帰納型の族

ある添字集合 `Λ : Type` の要素 `λ : Λ` のそれぞれに対して、型 `T λ : Sort u` を独立した型として定義することができます。簡単な例として、長さを型の情報として持つリストがあります。
-/

/-- 長さを型の情報として持つリスト -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : Vec α (n + 1)

/- これで帰納型の族 `{Vec α 0, Vec α 1, Vec α 2, …}` を定義したことになります。

`inductive` コマンドはパラメータと添字(index)を区別するため、次のように書くとエラーになることに注意してください。
-/

/--
error: inductive datatype parameter mismatch
  0
expected
  n
-/
#guard_msgs in
  inductive BadVec (α : Type) (n : Nat) : Type where
    | nil : BadVec α 0
    | cons (a : α) {n : Nat} (v : Vec α n) : BadVec α (n + 1)

/- このようにコードを書くと `n` はパラメータとして扱われます。パラメータは、各コンストラクタの返り値の型に一様に現れなくてはいけません。
したがって、`nil` の右辺には `BadVec α 0` ではなく `BadVec α n` が来なければならないというエラーが出ているわけです。実際に、このエラーはコンストラクタの返り値の型を変更すれば消すことができます。
-/

/-- 良くない方法でエラーを消した `BadVec` -/
inductive BadVec' (α : Type) (n : Nat) : Type where
  | nil : BadVec' α n
  | cons (a : α) (v : Vec α n) : BadVec' α n

#check (BadVec'.nil : BadVec' Nat 3)

/- しかし、元々の `Vec` とは似て非なるものになってしまいます。上記の `BadVec'` では、`nil : BadVec α 0` だけでなく `nil : BadVec α 1` や `nil : BadVec α 2` なども存在すると宣言したことになってしまいます。-/

/- ### 帰納的述語
帰納型を使って命題や述語を定義することもできます。作為的ではありますが簡単な例として、自然数が偶数であることを表す命題が挙げられます。
-/

/-- 自然数が偶数であることを表す帰納的述語 -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | add_two : ∀ n, Even n → Even (n + 2)

/- この場合 `inductive` コマンドを使用せずに、`def` を使って再帰関数として定義しても同じことができます。 -/

/-- 自然数が偶数であることを表す再帰関数 -/
def even : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => even n

/- 両者の違いは何でしょうか？双方にメリットとデメリットがあります。

再帰関数として定義するメリットとして、計算可能になることが挙げられます。再帰関数として定義されていれば [`#eval`](#{root}/Reference/Diagnostic/Eval.md) コマンドなど、Lean に組み込まれた機能を使って計算を行うことができます。一方で帰納的述語として定義されていると、計算をさせるための準備をこちらで行う必要があります。-/

-- すぐに計算できる
#guard even 4

/--
error: failed to synthesize
  Decidable (Even 4)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #eval Even 4

/-
帰納的述語として定義するメリットとしては、再帰が停止することを保証しなくて良いことが挙げられます。実際、帰納的述語は本質的に停止する保証がない再帰的な操作でも扱うことができます。以下は、少し複雑ですがプログラムの BigStep 意味論を表現する例です。[^hitchhiker]
-/

/-- 変数。ここでは簡単のために、すべての文字列が変数として存在するものとする -/
abbrev Variable := String

/-- プログラムの状態。すべての変数の値を保持したもの。
ここでは簡単にするために、変数の値はすべて自然数だとしている。 -/
def State := Variable → Nat

/-- `1 + x` のような算術式。変数の値を決めるごとに値が決まる。-/
def Arith := State → Nat

/-- 抽象化された単純なプログラミング言語のプログラム -/
inductive Stmt : Type where
  /-- 何もしないコマンド -/
  | skip : Stmt
  /-- `x := a` のような代入文。-/
  | assign : Variable → Arith → Stmt
  /-- 2つのコマンドを続けて実行する。`;;` で表される。-/
  | seq : Stmt → Stmt → Stmt
  /-- while 文 -/
  | whileDo : (State → Prop) → Stmt → Stmt

@[inherit_doc] infix:60 ";; " => Stmt.seq

-- 技術的な理由で必要
set_option quotPrecheck false in

/-- 状態 `s : State` があったとき、変数 `x` に対してだけ値を更新したものを表す記法 -/
notation s:70 "[" x:70 "↦" n:70 "]" => (fun v ↦ if v = x then n else s v)

open Stmt

/-- プログラムの BigStep 意味論。`BigStep c s t` は、
プログラム `c` を状態 `s` の下で実行すると状態が `t` になって停止することを表す。
-/
inductive BigStep : Stmt → State → State → Prop where
  /-- skip コマンドの意味論。-/
  | skip (s : State) : BigStep skip s s

  /-- 代入文 `x := a` の実行前に状態が `s` であったなら、
  代入文の実行後には状態は変数 `x` についてだけ更新される。-/
  | assign (x : Variable) (a : State → Nat) (s : State) :
    BigStep (assign x a) s (s[x ↦ a s])

  /-- seq コマンドの意味論。-/
  | seq {S T : Stmt} {s t u : State} (hS : BigStep S s t) (hT : BigStep T t u) :
    BigStep (S;; T) s u

  /-- while 文の、条件式が真のときの意味論。
  `whileDo B S` は、開始時に `B` が成り立っているなら、
  `S` を実行してから `whileDo B S` を実行するのと同じ意味になる。-/
  | while_true {B S s t u} (hcond : B s) (hbody : BigStep S s t)
    (hrest : BigStep (whileDo B S) t u) : BigStep (whileDo B S) s u

  /-- while 文の、条件式が偽のときの意味論。-/
  | while_false {B S s} (hcond : ¬ B s) : BigStep (whileDo B S) s s

/- 「プログラムを評価する」という操作は `while` 文の評価が終わらない可能性があるため、再帰関数として定義することができません。そのため上記の BigStep 意味論の例は帰納的述語が真に有用なケースであるといえます。-/

/- ## Peano の公理と帰納型

### 帰納型の仕様
帰納型を利用すると、「Peano の公理に基づく自然数の定義」のような帰納的な公理による定義を表現することができます。

Peano の公理とは、次のようなものです:
* `0` は自然数。
* 後者関数と呼ばれる関数 `succ : ℕ → ℕ` が存在する。
* 任意の自然数 `n` に対して `succ n ≠ 0` が成り立つ。
* `succ` 関数は単射。つまり2つの異なる自然数 `n` と `m` に対して `succ n ≠ succ m` が成り立つ。
* 帰納法の原理が成り立つ。つまり、任意の述語 `P : ℕ → Prop` に対して `P 0` かつ `∀ n : ℕ, P n → P (succ n)` ならば `∀ n : ℕ, P n` が成り立つ。

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
info: recursor MyNat.rec.{u} : {motive : MyNat → Sort u} →
  motive MyNat.zero → ((n : MyNat) → motive n → motive n.succ) → (t : MyNat) → motive t
-/
#guard_msgs in #print MyNat.rec

/- ### 帰納法の原理が意味するもの

ところで、Peano の公理の中でも帰納法の原理だけが述語に対する量化を含んでいて複雑ですね。複雑さのために何を意味しているのかわかりづらくなっているので、帰納法の原理から何が導かれるか考えてみます。

たとえば、帰納法の原理から「すべての `n : MyNat` は `.zero` か `.succ m` のどちらかの形である」ことが導かれます。これの証明は `inductive` コマンドを使用するとどこで帰納法の原理を使ったかわからなくなるので、以下では `axiom` コマンドで `MyNat` を再構築して証明しています。
-/
namespace Hidden --#

opaque MyNat : Type

/-- ゼロ -/
axiom MyNat.zero : MyNat

/-- 後者関数 -/
axiom MyNat.succ : MyNat → MyNat

/-- ゼロと後者関数の像が交わることはない -/
axiom MyNat.succ_ne_zero (n : MyNat) : MyNat.succ n ≠ MyNat.zero

/-- 後者関数は単射 -/
axiom MyNat.succ_inj {n m : MyNat} : MyNat.succ n = MyNat.succ m → n = m

/-- 帰納法の原理 -/
axiom MyNat.induction {P : MyNat → Prop}
  (h0 : P MyNat.zero) (hs : ∀ n, P n → P (MyNat.succ n)) : ∀ n, P n

example (n : MyNat) : n = MyNat.zero ∨ ∃ m, n = MyNat.succ m := by
  -- 述語の定義
  let P : MyNat → Prop := fun n => n = MyNat.zero ∨ ∃ m, n = MyNat.succ m

  -- `∀ n, P n` を示せばよい。
  suffices goal : ∀ n, P n from by
    exact goal n

  have h0 : P MyNat.zero := by
    simp [P]

  have hs : ∀ n, P n → P (MyNat.succ n) := by
    intro n hn
    dsimp [P]
    right
    exists n

  -- 帰納法の原理から従う
  intro n
  exact MyNat.induction h0 hs n

end Hidden --#
/- また、「`.succ n = n` となる `n : MyNat` は存在しない」ということも帰納法の原理から証明できます。-/

example (n : MyNat) : MyNat.succ n ≠ n := by
  intro h
  induction n with
  | zero => injection h
  | succ n ih =>
    have : n.succ = n := by injection h
    exact ih this

/- [^hitchhiker]: [The Hitchhiker’s Guide to Logical Verification](https://github.com/blanchette/interactive_theorem_proving_2024) を参考にいたしました。-/
