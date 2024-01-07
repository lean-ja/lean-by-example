import Aesop -- `aesop` のために必要
import Mathlib.Init.Function -- `Injection` のために必要
import Mathlib.Tactic.LibrarySearch -- `exact?` を使うために必要
import Mathlib.Tactic.Says -- `says` を使うために必要

-- `says` のチェックを有効にする
set_option says.verify true

/-!
  ## says

  検索タクティク `X` があり，その提案内容が `Try this: Y` だったとき，
  `X says` とすると `says` は `Try this: Y` の代わりに
  `Try this: X says Y` という提案を infoview 上で出します．
  それをクリックすると，`X says` の内容が `X says Y` で置換されます．
  そして，`X says Y` が実行されるときには `X` は飛ばされます．
-/

variable (P Q R S: Prop)

-- `exact?` に対して使用する例
example (hPQ : P → Q) (hQR : Q → R) (hRS : R → S) (hP : P) : S := by
  -- `exact?` は実行されない
  exact? says
    exact hRS (hQR (hPQ hP))

/-!
  ## aesop に使用した例

  `says` は `Try this: ...` と何かを提案するタクティクに対して有用です．
  `simp?`, `aesop?`, `exact?`, `apply?` などが該当します．
-/

-- 以下 `X` `Y` `Z`を集合とする
variable {X Y Z : Type}

open Function

/-- 合成 `g ∘ f` が単射なら，`f` も単射 -/
example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  aesop? says
    intro a₁ a₂ a
    apply hgfinj
    simp_all only [comp_apply]
