/- # Nat

`Nat` は自然数 `0, 1, 2, 3, ...` を表す型です。Lean では自然数としてゼロを含むことに注意してください。
数値リテラルはデフォルトで `Nat` の項として解釈されます。
-/

/-- info: 42 : Nat -/
#guard_msgs in #check 42

/- ## 定義

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

上記の `Nat` の定義では `zero` と `succ` という２つのコンストラクタを定義しているだけのように見えますが、コンストラクタの像が重ならないこと、コンストラクタが単射であること、帰納法の原理が成り立つことは `inductive` コマンドで定義した時点で暗黙のうちに保証されます。詳細は [`inductive`](#{root}/Declarative/Inductive.md) コマンドのページを参照してください。
-/

/- ## Nat 上の演算

`Nat` にも四則演算が定義されていますが、少し特殊な定義になっています。

`Nat` 上の引き算 `m - n` は返り値も `Nat` にならなければならないので、`n ≥ m` のとき `0` を返すように定義されています。
-/

-- ゼロを下回らないときは整数の引き算と一致する
#guard 32 - 4 = 28

-- ゼロを下回りそうなときはゼロになる
#guard 2 - 32 = 0
#guard 2 + (2 - 4) = 2

example (m n : Nat) (h : n ≥ m) : m - n = 0 := by omega

/- また `Nat` 上の割り算 `m / n` はゼロ除算を許すように定義されていて、`m / 0 = 0` が成り立ちます。-/

-- 割り切れるときの商
#guard 32 / 4 = 8

-- 割り切れないときは余りは切り捨て
#guard 32 / 15 = 2

-- ゼロ除算はゼロとして定義されている
#guard 2 / 0 = 0

-- 任意の数について `n / 0 = 0` が成り立つ
example (n : Nat) : n / 0 = 0 := by simp
