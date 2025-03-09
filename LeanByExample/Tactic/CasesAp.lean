/- # cases'

`cases'` は [`cases`](#{root}/Tactic/Cases.md) に似ていますが Lean3 の `cases` に近い挙動をします。証明を構造化するため、 `cases'` は使用しないことをお勧めします。
-/
import Mathlib.Tactic.Cases -- `cases'` を使用するために必要

variable {P Q R : Prop}

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR

  -- 場合分けをする
  cases' h with hP hQ
  · apply hPR hP
  · apply hQR hQ
