import Mathlib.Util.Whatsnew

/-- 0と1は等しくない -/
theorem Nat.one_neq_zero : 1 ≠ 0 := by
  simp

-- `[simp]`属性を追加したことによって、`(1 = 0) = False`という命題が追加されている
/-⋆-//--
info: theorem Nat.one_neq_zero._simp_1 : (1 = 0) = False :=
eq_false Nat.one_neq_zero

-- Lean.Meta.simpExtension extension: 1 new entries
-/
#guard_msgs in --#
whatsnew in attribute [simp] Nat.one_neq_zero

-- `simp`による書き換えの過程を表示する
set_option trace.Meta.Tactic.simp.rewrite true

/-⋆-//--
trace: [Meta.Tactic.simp.rewrite] Nat.succ_ne_self:1000:
      1 = 0
    ==>
      False
-/
#guard_msgs in --#
example (h : 1 = 0) : False := by
  simp at h
