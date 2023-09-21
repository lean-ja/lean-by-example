import Mathlib.Tactic.LibrarySearch

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Hom.Group.Defs


-- ANCHOR: first
-- 群順同型は積を保つ
example [Group G] [Group H] (f : G →* H) (a b : G) :
    f (a * b) = f a * f b := by
    -- `exact MonoidHom.map_mul f a b` を提案してくれる
    apply?
-- ANCHOR_END: first