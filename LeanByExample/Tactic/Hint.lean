/- # hint

`hint` は複数のタクティクを試し、上手くいったものを報告してくれるタクティクです。-/
import Mathlib.Tactic -- `hint` は検索を伴うので、おおざっぱに import している

/-⋆-//--
info: Try these:
  [apply] 🎉 simp_all only [forall_const]
  [apply] norm_num
  Remaining subgoals:
  ⊢ Q
  [apply] group
  Remaining subgoals:
  ⊢ Q
-/
#guard_msgs in --#
example (P Q : Prop) (p : P) (h : P → Q) : Q := by
  hint

/-⋆-//--
info: Try these:
  [apply] 🎉 simp_all only [and_self]
  [apply] norm_num
  Remaining subgoals:
  ⊢ Q ∧ P ∧ R
  [apply] group
  Remaining subgoals:
  ⊢ Q ∧ P ∧ R
-/
#guard_msgs in --#
example (P Q R : Prop) (x : P ∧ Q ∧ R ∧ R) : Q ∧ P ∧ R := by
  hint

/- ## 登録されているタクティク

`hint` に登録されているタクティクのリストは、`Mathlib.Tactic.Hint.getHints` 関数を介して確認することができます。
-/
open Lean Mathlib.Tactic in

/-- `hint` タクティクに登録されているタクティクの完全なリストを出力する -/
def getRegisteredTactics : CoreM Unit := do
  let hintTactics := (← Hint.getHints).map (fun (_n, tac) => tac.raw)
  for tactic in hintTactics do
    let .node _ _ arr := tactic
      | panic! "error: unexpected syntax term"
    IO.println arr[0]!

/-⋆-//--
info: "compute_degree"
"noncomm_ring"
"group"
"finiteness"
"linarith"
"field"
"field_simp"
"ring"
"positivity"
"bound"
"abel"
"norm_num"
"fun_prop"
"omega"
"decide"
"exact?"
"simp_all?"
"aesop"
"intro"
"split"
"tauto"
"trivial"
"grind"
"gcongr"
-/
#guard_msgs in --#
#eval getRegisteredTactics

/-
## タクティクの新規登録

登録されているタクティクに `tac` を追加するには、`register_hint tac` を実行します。
-/

register_hint 1000 nlinarith

/-⋆-//--
info: Try these:
  [apply] 🎉 nlinarith
-/
#guard_msgs in --#
example (a b : Nat) (h : a ≤ b) : (a + b) ^ 2 ≤ 4 * b ^ 2 := by
  hint
