/-
# itauto
`itauto` は、直観主義論理(intuitionistic logic)の範囲内でトートロジー(tautology)を証明します。[「Contraction-free sequent calculi for intuitionistic logic」](https://www.cs.cmu.edu/~fp/courses/atp/cmuonly/D92.pdf)という1992年の論文に基づいて実装されています。

命題論理を扱うタクティクには他にも [`tauto`](./Tauto.md) がありますが、あちらは選択原理 [`Classical.choice`](#{root}/Declarative/Axiom.md#ClassicalChoice) を勝手に使用することがあります。なお選択原理は Lean が標準で用意している公理のひとつで、排中律 `P ∨ ¬ P` や二重否定の除去 `¬¬ P → P` を示すのに必要です。
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
/-- info: 'not_iff_not₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_iff_not₁

/- [`tauto`](./Tauto.md) と同様に、扱えるのは命題論理のトートロジーだけです。述語論理は扱えないことがあります。-/

/-- 排中律の二重否定 -/
example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  -- `itauto` で示せる
  itauto

example : ∀ (P : Prop), ¬¬ (P ∨ ¬ P) := by
  -- 量化されただけで `itauto` で示せなくなる
  fail_if_success itauto

  intro P hP

  -- 量化がなくなると扱えるようになる
  itauto
