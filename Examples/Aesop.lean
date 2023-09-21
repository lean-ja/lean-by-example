-- `Injective` を使用するため
import Mathlib.Init.Function

import Aesop

-- 以下 `X` `Y` `Z`を集合とする
variable {X Y Z : Type}

open Function


-- ANCHOR: first
-- 合成 `g ∘ f` が単射なら，`f` も単射
example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  aesop
-- ANCHOR_END: first


-- ANCHOR: question
example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  -- `aesop?` は以下を返す
  intro a₁ a₂ a
  apply hgfinj
  simp_all only [comp_apply]
-- ANCHOR_END: question
