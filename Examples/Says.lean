import Aesop
import Mathlib.Init.Function
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Says

variable (P Q R S: Prop)

-- ANCHOR: first
example (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  -- `exact?` は実行されない
  exact? says exact hRS (hQR (hPQ hP))
-- ANCHOR_END: first


-- 以下 `X` `Y` `Z`を集合とする
variable {X Y Z : Type}

open Function

-- ANCHOR: aesop
-- 合成 `g ∘ f` が単射なら，`f` も単射
example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  aesop? says {
    intro a₁ a₂ a
    apply hgfinj
    simp_all only [comp_apply]
  }
-- ANCHOR_END: aesop