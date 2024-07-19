/- # hint

`hint` は複数のタクティクの中から提案を出してくれるタクティクです。デフォルトでは

* [`split`](./Split.md)
* [`intro`](./Intro.md)
* [`aesop`](./Aesop.md)
* `decide`
* [`exact?`](./ExactQuestion.md)
* `simp_all?`
* [`linarith`](./Linarith.md)

の7つのタクティクを同時に試します。

* ゴールを閉じることに成功したものは緑色で示され、
* 進捗があったものはウィジェットに新しいゴールを示します。-/
import Mathlib.Tactic -- `hint` は検索を伴うので、おおざっぱに import している

variable (P Q R : Prop) (a b : ℕ)

/--
info: Try these:
• linarith
-/
#guard_msgs in
example (h : 1 < 0) : False := by
  hint

/--
info: Try these:
• exact h p
-/
#guard_msgs in
example (p : P) (h : P → Q) : Q := by
  hint

/--
info: Try these:
• simp_all only [and_self]
-/
#guard_msgs in
example (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by
  hint

/--
info: Try these:
• linarith
-/
#guard_msgs in
example (h : a < b) : ¬ b < a := by
  hint

/--
info: Try these:
• omega
-/
#guard_msgs in
example : 37^2 - 35^2 = 72 * 2 := by
  hint

/--
info: Try these:
• decide
-/
#guard_msgs in
example : Nat.Prime 37 := by
  hint

/-!
## タクティクの新規登録

登録されているタクティクに `tac` を追加するには、`register_hint tac` を実行します。
-/

register_hint nlinarith

/--
info: Try these:
• nlinarith
-/
#guard_msgs in
example (h : a ≤ b) : (a + b) ^ 2 ≤ 4 * b ^ 2 := by
  hint
