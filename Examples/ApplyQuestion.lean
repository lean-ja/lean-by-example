import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Hom.Group.Defs
import Mathlib.Tactic.Explode
import Mathlib.Tactic.LibrarySearch


-- ANCHOR: first
-- 群準同型は積を保つ
example [Group G] [Group H] (f : G →* H) (a b : G) :
    f (a * b) = f a * f b := by
    -- `exact MonoidHom.map_mul f a b` を提案してくれる
    apply?
-- ANCHOR_END: first


-- ANCHOR: sorry
theorem T (x y : Nat) (h: x ≤ y) : 2 ^ x ≤ 2 ^ y := by
    apply?

    -- `apply?` しただけで `done` が通り，示せているように見える
    done

/-
T : ∀ (x y : ℕ), x ≤ y → 2 ^ x ≤ 2 ^ y

0│       │ x       ├ ℕ
1│       │ y       ├ ℕ
2│       │ h       ├ x ≤ y
3│       │ sorryAx │ 2 ^ x ≤ 2 ^ y
4│0,1,2,3│ ∀I      │ ∀ (x y : ℕ), x ≤ y → 2 ^ x ≤ 2 ^ y
-/
#explode T
-- ANCHOR_END: sorry