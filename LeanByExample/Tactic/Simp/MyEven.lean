import Mathlib.Util.WhatsNew

/-- 偶数を表す帰納的述語 -/
inductive MyEven : Nat → Prop where
  | zero : MyEven 0
  | step (n : Nat) : MyEven n → MyEven (n + 2)

theorem MyEven_two : MyEven 2 := by
  apply MyEven.step
  apply MyEven.zero

-- `MyEven 2 = True` という書き換えルールが自動生成されている
/-⋆-//--
info: theorem MyEven_two._simp_1 : MyEven 2 = True :=
eq_true MyEven_two

-- Lean.Meta.simpExtension extension: 1 new entries
-/
#guard_msgs in --#
whatsnew in attribute [simp] MyEven_two

-- `simp`による書き換えの過程を表示する
set_option trace.Meta.Tactic.simp.rewrite true

/-⋆-//--
trace: [Meta.Tactic.simp.rewrite] MyEven_two:1000:
      MyEven 2
    ==>
      True
-/
#guard_msgs in --#
example : MyEven 2 := by
  simp
