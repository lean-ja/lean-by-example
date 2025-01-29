/- # cases

`cases` は場合分けを行うことができるタクティクです。

たとえば、ローカルコンテキストに `h : P ∨ Q` があるときに `cases h` とすると、仮定に `P` を付け加えたゴール `case inl` と、仮定に `Q` を付け加えたゴール `case inr` を生成します。

上位互換にあたるタクティクに [`rcases`](./Rcases.md) があります。
-/

-- `P`, `Q`, `R` を命題とする
variable (P Q R : Prop)

example : P ∨ Q → (P → R) → (Q → R) → R := by
  -- `h: P ∨ Q`
  intro h hPR hQR

  -- `case inl` と `case inr` の２つのゴールを生成する
  cases h

  -- `P` が成り立つ場合
  case inl hP =>
    exact hPR hP

  -- `Q` が成り立つ場合
  case inr hQ =>
    exact hQR hQ

/- ## with を使う書き方

`case` を使わずに、`with` を使って次のように書くこともできます
-/

example : P ∨ Q → (P → R) → (Q → R) → R := by
  -- `h: P ∨ Q`
  intro h hPR hQR

  -- `case inl` と `case inr` の２つのゴールを生成する
  cases h with
  | inl hP =>
    exact hPR hP
  | inr hQ =>
    exact hQR hQ

/- ## 舞台裏

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
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

end Hidden --#
