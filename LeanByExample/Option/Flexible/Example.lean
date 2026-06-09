import Mathlib.Tactic.Linter.FlexibleLinter

set_option linter.flexible true

/--
warning: `simp` is a flexible tactic modifying `⊢`. Try `simp?` and use the suggested `simp only [...]`. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
-/
#guard_msgs (warning) in --#
example {n m : Nat} (h : n = m) : True ∧ (n = m) := by
  simp
  exact h

example {n m : Nat} (h : n = m) : True ∧ (n = m) := by
  -- 書き換えると警告が消える
  simpa
