import Mathlib.Tactic.Cases -- `cases'` を使用するために必要
import Std.Tactic.RCases -- `rcases` を使用するために必要

-- `P`, `Q`, `R` を命題とする
variable (P Q R : Prop)

/-! ## cases -/

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

/-!
  ## with を使う書き方

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

  `cases` は，実際には論理和に限らず
  inductive type をコンストラクタに分解することができるタクティクです．
  論理和を分解することができるのも，
  `Or` が inductive type として定義されているからです．
-/

-- `Or` の定義を `#print` コマンドで確認できます.

/-
inductive Or : Prop → Prop → Prop
number of parameters: 2
constructors:
Or.inl : ∀ {a b : Prop}, a → a ∨ b
Or.inr : ∀ {a b : Prop}, b → a ∨ b
-/
#print Or

/-!
  ## cases'

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

/-!
  ## rcases

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
