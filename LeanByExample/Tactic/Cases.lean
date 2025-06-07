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
