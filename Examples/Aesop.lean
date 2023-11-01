import Aesop -- `aesop` を使用するため
import Mathlib.Init.Function -- `Injective` を使用するため
import Mathlib.Tactic.Says -- `says` を使用するため

-- CI 環境で `says` のチェックをしない
set_option says.no_verify_in_CI true

-- 以下 `X` `Y` `Z`を集合とする
variable {X Y Z : Type}

open Function

/-! ## aesop -/

-- 合成 `g ∘ f` が単射なら，`f` も単射
example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  show ∀ ⦃a₁ a₂ : X⦄, f a₁ = f a₂ → a₁ = a₂

  -- 示すべきことがまだまだあるように見えるが，一発で証明が終わる
  aesop

/-!
  ## aesop?

  aesop が成功するとき，aesop? に置き換えると，
  ゴールを達成するのにどんなタクティクを使用したか教えてくれる．
-/

example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]

  -- 注意: ここでは説明のために `says` を使用するが，
  -- 単に `aesop?` とするだけで提案が見られる
  aesop? says
    intro a₁ a₂ a
    apply hgfinj
    simp_all only [comp_apply]
