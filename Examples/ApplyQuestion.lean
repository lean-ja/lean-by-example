import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Hom.Group.Defs
import Mathlib.Tactic.LibrarySearch -- apply? を使うのに必要

/-- 群準同型は積を保つ -/
example [Group G] [Group H] (f : G →* H) (a b : G) :
    f (a * b) = f a * f b := by
  -- `exact MonoidHom.map_mul f a b` を提案してくれる
  apply?

/-!
  ## 補足

  `apply?` はあくまで証明を書くときに補助として使うものです．
  `sorry` と同じように，清書した証明に残してはいけません．
  `sorry` と同じと言いましたが，実際 `apply?` は `sorryAx` を裏で使用します．
-/

theorem T (x y : Nat) (_: x ≤ y) : 2 ^ x ≤ 2 ^ y := by
  apply?

  -- `apply?` しただけで `done` が通り，示せているように見える
  done

-- 以下に示すように，裏で `sorryAx` が使われている

/- 'T' depends on axioms: [sorryAx] -/
#print axioms T
