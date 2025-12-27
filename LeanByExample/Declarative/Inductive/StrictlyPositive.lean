import Mathlib.SetTheory.Cardinal.Basic

-- 任意に型 A が与えられたとして固定する
opaque A : Type

/-- strictly positive 要件を破っている帰納型 -/
unsafe inductive Bad where
  | mk (f : Bad → A)

section
  /- ## A が空の場合

  `A` が空なら、`A` は `False` と同じなので矛盾が導かれる。
  -/

  unsafe def selfApply (b : Bad) : A :=
    match b with
    | Bad.mk f => f b

  -- A の項が A の情報を使わずに構成できてしまった
  unsafe def ω : A := selfApply (Bad.mk selfApply)

  /-- `A` が空なら矛盾が導かれる -/
  unsafe example [IsEmpty A] : False :=
    IsEmpty.false ω
end

section
  /- ## A に２つ以上の要素があるとき -/

  /-- `Bad` と `Bad → A` の間に全単射がある -/
  unsafe def equiv : Bad ≃ (Bad → A) where
    toFun := fun ⟨f⟩ => f
    invFun := Bad.mk
    left_inv := by
      intro ⟨f⟩
      rfl
    right_inv := by
      intro f
      rfl

  open scoped Cardinal

  unsafe example [Nontrivial A] : False := by
    -- `Bad` と `Bad → A` は全単射があるので濃度(`#`)が同じ
    have h : # Bad = # (Bad → A) :=
      Cardinal.mk_congr equiv

    -- 特に、`# Bad = # A ^ # Bad` が成り立つ
    replace h : # Bad = #A ^ # Bad := by
      simpa [Cardinal.mk_pi, Cardinal.prod_const, Cardinal.lift_id] using h

    -- しかしカントール(Cantor)の定理により、`# A ≥ 2` ならば
    -- `# Bad < # A ^ # Bad` が成り立つ
    have : # Bad < #A ^ # Bad := by
      apply Cardinal.cantor' (a := # Bad) (b := # A)
      rw [Cardinal.one_lt_iff_nontrivial]
      infer_instance

    -- これは矛盾
    apply ne_of_lt this h
end

-- ω を簡約すると ω 自身が出てくる
-- つまり無限ループしている
/-⋆-//--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in --#
#reduce ω
