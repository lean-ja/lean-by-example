import Mathlib.Algebra.Group.Defs -- `add_zero` を使用するため

variable (X : Type)

-- ANCHOR: first
example (f : Int → X) (h : x = 0) : f (2 + x) = f 2 := by
  congr
  show 2 + x = 2

  simp only [h, add_zero]
-- ANCHOR_END: first


-- ANCHOR: option
example (f : Int → Int) (g : Int → X) (h : x = 0)
  (hf : ∀ x, f x = f (- x)) : g (f (2 + x)) = g (f (- 2)) := by
  -- 仮に `congr` とすると
  -- ゴールが `⊢ 2 + x = -2` になってしまう

  congr 1
  show f (2 + x) = f (-2)

  simp only [h, add_zero]
  exact hf _
-- ANCHOR_END: option
