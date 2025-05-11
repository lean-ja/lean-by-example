/- # hint

`hint` は複数のタクティクを試し、上手くいったものを報告してくれるタクティクです。-/
import Mathlib.Tactic -- `hint` は検索を伴うので、おおざっぱに import している

/-⋆-//--
info: Try these:
• bound
• group
• ring_nf
• norm_num
-/
#guard_msgs in --#
example (P Q : Prop) (p : P) (h : P → Q) : Q := by
  hint

/-⋆-//--
info: Try these:
• bound
• group
• ring_nf
• norm_num
-/
#guard_msgs in --#
example (P Q R : Prop) (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by
  hint

/- ## 登録されているタクティク
デフォルトでは以下の18個のタクティクを試します。

* `group`
* `noncomm_ring`
* [`gcongr`](./Gcongr.md)
* [`ring`](./Ring.md)
* [`linarith`](./Linarith.md)
* `norm_num`
* [`positivity`](./Positivity.md)
* `bound`
* `abel`
* [`omega`](./Omega.md)
* [`decide`](./Decide.md)
* [`exact?`](./ExactQuestion.md)
* `simp_all?`
* [`aesop`](./Aesop.md)
* [`intro`](./Intro.md)
* [`split`](./Split.md)
* [`tauto`](./Tauto.md)
* [`trivial`](./Trivial.md)

`hint` に登録されているタクティクのリストは、`Mathlib.Tactic.Hint.getHints` 関数を介して確認することができます。
-/
open Lean in

/-- `hint` タクティクに登録されているタクティクの完全なリストを出力する -/
def getRegisteredTactics : CoreM Unit := do
  let hintTactics := (← Mathlib.Tactic.Hint.getHints).map (·.raw)
  for tactic in hintTactics do
    let .node _ _ arr := tactic
      | panic! "error: unexpected syntax term"
    IO.println arr[0]!

/-⋆-//--
info: "group"
"noncomm_ring"
"gcongr"
"ring"
"linarith"
"norm_num"
"positivity"
"bound"
"abel"
"omega"
"decide"
"exact?"
"simp_all?"
"aesop"
"intro"
"split"
"tauto"
"trivial"
-/
#guard_msgs in --#
#eval getRegisteredTactics

/-
## タクティクの新規登録

登録されているタクティクに `tac` を追加するには、`register_hint tac` を実行します。
-/

register_hint nlinarith

/-⋆-//--
info: Try these:
• nlinarith
-/
#guard_msgs in --#
example (a b : Nat) (h : a ≤ b) : (a + b) ^ 2 ≤ 4 * b ^ 2 := by
  hint
