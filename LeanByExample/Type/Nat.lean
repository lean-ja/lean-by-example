/- # Nat

`Nat` は自然数 `0, 1, 2, 3, ...` を表す型です。Lean では自然数としてゼロを含むことに注意してください。
`Nat` の項は、数値リテラルとして表現することができます。
-/

/-⋆-//-- info: 42 : Nat -/
#guard_msgs in --#
#check 42

/- ## Peano の公理

Lean の標準ライブラリにおいて、`Nat` は [`inductive`](#{root}/Declarative/Inductive.md) コマンドを使って以下のように定義されています。 -/

--#--
/--
info: inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
-/
#guard_msgs in #print Nat
--#--
namespace Hidden --#

inductive Nat where
  /-- ゼロ -/
  | zero : Nat
  /-- 後者関数 -/
  | succ (n : Nat) : Nat

end Hidden --#
/- これは Peano の公理に則ったものです。思い出してみると Peano の公理とは、次のようなものでした:

* `0` は自然数。
* 後者関数と呼ばれる関数 `succ : ℕ → ℕ` が存在する。
* 任意の自然数 `n` に対して `succ n ≠ 0` が成り立つ。
* `succ` 関数は単射。つまり2つの異なる自然数 `n` と `m` に対して `succ n ≠ succ m` が成り立つ。
* 帰納法の原理が成り立つ。つまり、任意の述語 `P : ℕ → Prop` に対して `P 0` かつ `∀ n : ℕ, P n → P (succ n)` ならば `∀ n : ℕ, P n` が成り立つ。

一見すると、上記の `Nat` を定義するコードは不完全なように見えます。ゼロが自然数であること、後者関数が存在することは明示的に表現されているのでわかりますが、他の条件が表現されているかどうかは一見して明らかではありません。

しかし、実は他の条件も暗黙のうちに表現されています。コンストラクタの像が重ならないこと、コンストラクタが単射であること、帰納法の原理が成り立つことは [`inductive`](#{root}/Declarative/Inductive.md) コマンドで定義した時点で暗黙のうちに保証されているからです。
-/
/- ## 帰納法の原理の帰結

ところで、Peano の公理の中でも帰納法の原理だけが述語に対する量化を含んでいて複雑ですね。複雑さのために何を意味しているのかわかりづらくなっているので、帰納法の原理から何が導かれるか考えてみます。

たとえば、帰納法の原理から「すべての `n : MyNat` は `.zero` か `.succ m` のどちらかの形である」ことが導かれます。以下の証明では [`axiom`](#{root}/Declarative/Axiom.md) コマンドで `MyNat` を再構築することで証明しています。これは、`inductive` コマンドで定義された型に対しては、[`cases`](#{root}/Tactic/Cases.md) タクティクでコンストラクタに応じた場合分けが自動的にできてしまうからです。
-/
namespace Hidden --#

opaque MyNat : Type

/-- ゼロ -/
axiom MyNat.zero : MyNat

/-- 後者関数 -/
axiom MyNat.succ : MyNat → MyNat

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
/- また、「`.succ n = n` となる `n : MyNat` は存在しない」ということも帰納法の原理から導かれます。-/

inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

example (n : MyNat) : MyNat.succ n ≠ n := by
  intro h
  induction n with
  | zero => injection h
  | succ n ih =>
    exact ih (show n.succ = n from by injection h)
/- ## Nat 上の演算

`Nat` にも四則演算が定義されていますが、少し特殊な定義になっています。

### 引き算

`Nat` 上の引き算 `m - n` は返り値も `Nat` にならなければならないので、`n ≥ m` のとき `0` を返すように定義されています。
-/

-- ゼロを下回らないときは整数の引き算と一致する
#guard 32 - 4 = 28

-- ゼロを下回りそうなときはゼロになる
#guard 2 - 32 = 0
#guard 2 + (2 - 4) = 2

example (m n : Nat) (h : n ≥ m) : m - n = 0 := by omega

/- `Nat` における引き算は誤解を招きやすいので、注意深く避けた方が良いかもしれません。[^fermat] -/
section
  /- ## Nat における引き算が誤解を招くものであるという例 -/

  variable (x y z n : Nat)

  -- 一瞬、Fermat の最終定理が `omega` 一発で示せてしまったかのように見える。
  -- しかし `2 - n < 0` となることはありえないので、この仮定は偽で、
  -- 偽の仮定があるから証明が通っているだけ。
  theorem Fermat (h1 : 2 - n < 0) : x ^ n + y ^ n = z ^ n → (x * y * z = 0) := by
    omega

end
/- ### 割り算
また `Nat` 上の割り算 `m / n` はゼロ除算を許すように定義されていて、`m / 0 = 0` が成り立ちます。-/

-- 割り切れるときの商
#guard 32 / 4 = 8

-- 割り切れないときは余りは切り捨て
#guard 32 / 15 = 2

-- ゼロ除算はゼロとして定義されている
#guard 2 / 0 = 0

-- 任意の数について `n / 0 = 0` が成り立つ
example (n : Nat) : n / 0 = 0 := by simp

/- ゼロ除算が許されているのが奇妙に感じるでしょうか？Lean では、以下のように分母がゼロではないことを検証するような割り算を実装することもできます。-/

/-- 分母がゼロでないことを `decide` タクティクで検証する、安全な割り算 -/
def safeDiv (m n : Nat) (_nez : n ≠ 0 := by decide) : Nat :=
  m / n

#eval safeDiv 32 4

-- ゼロで割ろうとすると、分母がゼロでないことが確かめられないというエラーになる
#check_failure safeDiv 32 0

/- 他にも返り値を [`Option`](#{root}/Type/Option.md) で包んだり、ゼロ除算をしたときに `panic!` を呼び出したりすることが考えられます。しかし、いずれも除算を呼び出すたびにゼロかどうかの場合分けが発生してしまうのが手間です。現行の定義であれば、ゼロ除算をチェックするのは関数を呼び出す時ではなくて定理を適用する時だけで済みます。-/

/- [^fermat]: このコード例は Lean の公式 Zulip の Fermat Last theorem by omega というトピックで [Anton Mellit さんが示したコード例](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Fermat.20Last.20theorem.20by.20omega/near/471640946)を参考にしています。 -/
