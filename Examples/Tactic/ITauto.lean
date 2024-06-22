/-
# itauto
`itauto` は，直観主義論理(intuitionistic logic)の範囲内でトートロジー(tautology)を証明します．

命題論理を扱うタクティクには他にも [`tauto`](./Tauto.md) がありますが，あちらは選択原理(`Classical.choice`)を勝手に使用することがあります．なお選択原理は Lean が標準で用意している公理のひとつで，排中律 `P ∨ ¬ P` や二重否定の除去 `¬ ¬ P → P` を示すのに必要です．
-/
import Mathlib.Tactic.ITauto
import Mathlib.Tactic.Tauto

-- 命題とその否定は同値ではない
-- itauto で示したバージョン
theorem not_iff_not₀ (p : Prop) : ¬ (p ↔ ¬ p) := by itauto

-- tauto で示したバージョン
theorem not_iff_not₁ (p : Prop) : ¬ (p ↔ ¬ p) := by tauto

-- 選択原理に依存していない
/-- info: 'not_iff_not₀' does not depend on any axioms -/
#guard_msgs in #print axioms not_iff_not₀

-- 勝手に選択原理を使用している！
/-- info: 'not_iff_not₁' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in #print axioms not_iff_not₁
