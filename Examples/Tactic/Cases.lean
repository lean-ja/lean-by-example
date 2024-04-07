/- # cases

`cases` は場合分けを行うことができるタクティクです．

たとえば，ローカルコンテキストに `h : P ∨ Q` があるときに `cases h` とすると，仮定に `P` を付け加えたゴール `case inl` と，仮定に `Q` を付け加えたゴール `case inr` を生成します．

補足すると，`inl` と `inr` はそれぞれ `left injection` と `right injection` からその名前があり，`Or` 型のコンストラクタです．-/
import Mathlib.Tactic.Cases -- `cases'` を使用するために必要 --#

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

/-! ## with を使う書き方

`case` を使わずに，`with` を使って次のように書くこともできます
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

/-!
## 補足

`cases` は，実際には論理和に限らず帰納型をコンストラクタに分解することができるタクティクです．
論理和を分解することができるのも，`Or` が帰納型として定義されているからです．
-/
namespace Cases --#

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

end Cases --#
/-! ## cases'

`cases'` というタクティクもあります．
こちらは lean3 の `cases` に近い挙動をします．
証明を構造化するため， `cases'` は使用しないことをお勧めします．
-/

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR

  -- 場合分けをする
  cases' h with hP hQ
  · apply hPR hP
  · apply hQR hQ

/-! ## rcases

`rcases` は `cases` をパターンに従って再帰的(recursive)に適用します．
-/

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR

  -- 場合分けをする
  rcases h with hP | hQ
  · apply hPR hP
  · apply hQR hQ

-- 論理積 ∧ に対しても使えます
example : P ∧ Q → Q ∧ P := by
  -- `h: P ∧ Q` と仮定する
  intro h

  -- `h: P ∧ Q` を `hP: P` と `hQ: Q` に分解する
  rcases h with ⟨hP, hQ⟩

  -- `Q ∧ P` を証明する
  exact ⟨hQ, hP⟩
