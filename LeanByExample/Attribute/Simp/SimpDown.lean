
/-- 整数のような何か -/
opaque MyInt : Type

variable [LE MyInt] [Add MyInt] [Zero MyInt]

@[simp]
axiom MyInt.add_zero (a : MyInt) : a + 0 = a

@[simp]
axiom MyInt.simp_le_add (a b c : MyInt) : a + b ≤ a + c ↔ b ≤ c

set_option warn.sorry false in --#

example (a b : MyInt) (h : a + 0 ≤ a + b) : 0 ≤ b := by
  simp at h

  -- `simp` により `add_zero` が先に適用されてしまう
  -- 本当は `simp_le_add` が先に適用されて欲しい…
  guard_hyp h : a ≤ a + b

  sorry

-- `[simp↓]` 属性を付与する
attribute [simp↓] MyInt.simp_le_add

-- `simp`の行った書き換えを追跡する
set_option trace.Meta.Tactic.simp.rewrite true

/-⋆-//--
trace: [Meta.Tactic.simp.rewrite] ↓ MyInt.simp_le_add:1000:
      a + 0 ≤ a + b
    ==>
      0 ≤ b
-/
#guard_msgs in --#
example (a b : MyInt) (h : a + 0 ≤ a + b) : 0 ≤ b := by
  -- ちゃんと `simp_le_add` が先に適用されるようになった！
  simp at h
  assumption
