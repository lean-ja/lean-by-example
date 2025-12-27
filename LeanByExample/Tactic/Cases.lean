/- # cases

`cases` は場合分けを行うことができるタクティクです。

たとえば、ローカルコンテキストに `h : P ∨ Q` があるときに `cases h` とすると、仮定に `P` を付け加えたゴールと、仮定に `Q` を付け加えたゴールをそれぞれ生成します。

よく似たタクティクに [`rcases`](./Rcases.md) があります。
-/

example (P Q R : Prop) : P ∨ Q → (P → R) → (Q → R) → R := by
  -- `h: P ∨ Q`
  intro h hPR hQR

  -- `inl` と `inr` の２つのゴールを生成する
  cases h with

  -- `P` が成り立つ場合
  | inl hP =>
    exact hPR hP

  -- `Q` が成り立つ場合
  | inr hQ =>
    exact hQR hQ

/- `=>` を省略することもできます。 -/

example (P Q R : Prop) : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR

  cases h with | inl hP | inr hQ

  · exact hPR hP
  · exact hQR hQ

/- ## case タクティク

`cases .. with` 構文を使わずに、`case` タクティクを使って次のように書くこともできます。
-/

example (P Q R : Prop) : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR

  cases h

  case inl hP =>
    apply hPR
    assumption

  case inr hQ =>
    apply hQR
    assumption

/- ## 舞台裏

### 帰納型の分解

`cases` は、実際には論理和に限らず[帰納型](#{root}/Declarative/Inductive.md)をコンストラクタに分解することができるタクティクです。
-/

-- 帰納型として定義した例示のための型
inductive Sample where
  | foo (x y : Nat)
  | bar (z : String)

example (s : Sample) : True := by
  -- cases で場合分けを実行できる
  cases s

  case foo x y =>
    trivial

  case bar z =>
    trivial

/- 論理和を分解することができるのも、`Or` が次のように帰納型として定義されているからです。 -/
namespace Hidden --#

--#--
-- Or の定義が変わっていないことを確認するためのコード
/--
info: inductive Or : Prop → Prop → Prop
number of parameters: 2
constructors:
Or.inl : ∀ {a b : Prop}, a → a ∨ b
Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/
#guard_msgs in #print Or
--#--

inductive Or (a b : Prop) : Prop where
  | inl (h : a)
  | inr (h : b)

end Hidden --#
/-
### 帰納的述語の分解

特に、帰納的述語も `cases` タクティクで分解することができます。
仮定がどのコンストラクタから来たものなのかに応じて場合分けをすることができます。

たとえば、以下のように偶数であることを表す帰納的述語を定義したとします。
このとき `Even (n + 2)` という仮定があれば `Even n` を結論出来ますが、これは `cases` タクティクで行うことができます。
-/

/-- 偶数であることを表す帰納的述語 -/
inductive Even : Nat → Prop where
  | zero : Even 0
  | cons {n : Nat} (ih : Even n) : Even (n + 2)

example (n : Nat) (h : Even (n + 2)) : Even n := by
  -- h に対して場合分けを行う。
  -- `Even (n + 2)` という仮定はどのコンストラクタから来たか？で場合分けできる。
  -- `cases` タクティクはある程度賢いので、
  -- `zero` のケースはありえないと判断してスキップできる。
  cases h with
  | cons ih =>
    exact ih
