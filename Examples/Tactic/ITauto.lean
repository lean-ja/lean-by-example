/-
# itauto
`itauto` は，直観主義論理(intuitionistic logic)の範囲内でトートロジー(tautology)を証明します．
-/
import Mathlib.Tactic.ITauto

-- 命題とその否定は同値ではない
theorem not_iff_not (p : Prop) : ¬ (p ↔ ¬ p) := by itauto

/-- info: 'not_iff_not' does not depend on any axioms -/
#guard_msgs in #print axioms not_iff_not

-- カリー化
theorem currying (p q : Prop) : ¬ (p ∧ q) ↔ (p → ¬ q) := by itauto

/-- info: 'currying' does not depend on any axioms -/
#guard_msgs in #print axioms currying
