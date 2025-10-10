import LeanByExample.Type.Linter.DetectClassical

-- 選択原理を使用しているため警告が出る
/-⋆-//--
warning: `prop_iff_neg_self₀` depends on `Classical.choice`.
All axioms: [Classical.choice, propext, Quot.sound]

Note: This linter can be disabled with `set_option linter.detectClassical false`
-/
#guard_msgs in --#
theorem prop_iff_neg_self₀ (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h
  by_cases hp : P
  · have : ¬ P := by
      rwa [h] at hp
    contradiction
  · have : ¬ ¬ P := by
      rwa [h] at hp
    contradiction

-- 選択原理に依存しない証明には警告が出ない
#guard_msgs (warning) in --#
theorem prop_iff_neg_self₁ (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h
  have hnp : ¬ P := by
    intro hp
    have hnp : ¬ P := by
      rwa [h] at hp
    contradiction
  have hp : P := by
    have : ¬ ¬ P := by
      rwa [h] at hnp
    contradiction
  contradiction
