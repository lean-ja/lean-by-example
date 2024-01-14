/- # hint

`hint` は複数のタクティクの中から提案を出してくれるタクティクです．デフォルトでは

* [split](./Split.md)
* [intro](./Intro.md)
* [aesop](./Aesop.md)
* `decide`
* [exact?](./ExactQuestion.md)
* `simp_all?`
* [linarith](./Linarith.md)

の7つのタクティクを同時に試します．

* ゴールを閉じることに成功したものは緑色で示され，
* 進捗があったものはウィジェットに新しいゴールを示します．-/
import Mathlib.Tactic -- `hint` は検索を伴うので，おおざっぱに import している

variable (P Q R : Prop) (a b : ℕ)

example (h : 1 < 0) : False := by
  -- linarith
  hint

example (p : P) (h : P → Q) : Q := by
  -- exact h p
  hint

example (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by
  -- simp_all only [and_self]
  hint

example (h : a < b) : ¬ b < a := by
  -- linarith
  hint

example : 37^2 - 35^2 = 72 * 2 := by
  -- exact rfl
  hint

example : Nat.Prime 37 := by
  -- exact (Nat.prime_iff_card_units 37).mpr rfl
  hint

/-!
## タクティクの新規登録

登録されているタクティクに `tac` を追加するには，`register_hint tac` を実行します．
-/

register_hint nlinarith

example (h : a ≤ b) : (a + b) ^ 2 ≤ 4 * b ^ 2 := by
  -- nlinarith
  hint
