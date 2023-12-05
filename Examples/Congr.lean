import Mathlib.Tactic -- `simp` で利用できる補題を確保するため

variable (X : Type) (x : Int) (f : Int → Int)

/-! ## congr -/

example (h : x = 0) : f (2 + x) = f 2 := by
  congr
  show 2 + x = 2

  simp [h]

/-! ## congr の再帰の深さを調節する -/

example (g : Int → X) (h : x = 0) (hf : ∀ x, f x = f (- x)) :
    g (f (2 + x)) = g (f (- 2)) := by

  -- congr の再帰がアグレッシブすぎて上手くいかないことがある
  try (
    congr

    -- 分解しすぎた
    show 2 + x = -2

    -- これでは示すことができない
    fail
  )

  -- 再帰の深さを数値として指定できる
  congr 1

  -- ちょうどよい分解になった
  show f (2 + x) = f (-2)

  simp only [h, add_zero]
  exact hf _
