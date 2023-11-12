import Mathlib.Tactic.FieldSimp -- `field_simp` を使うのに必要
import Mathlib.Tactic.LibrarySearch -- `exact?` を使うのに必要
import Mathlib.Tactic.RewriteSearch -- `rw_search` のために必要
import Mathlib.Tactic.Ring -- `ring` を使うのに必要

/-! ## show ... from で証明を構成する -/

variable (a b x : ℚ)

/-! ### タクティクで証明を構成する例 -/

example (f : ℚ → ℕ) : f ((a + b) ^ 2) = f (a ^ 2 + 2 * a * b + b ^ 2) := by
  -- `have` をつかって補題を用意しなくても，
  -- `show ... from` で無名の証明を構成してそれを `rw` に渡すことができる
  rw [show (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 from by ring]

/-! ### 後から証明する例 -/

example (h : a * x < b) (ha : a > 0) : x < b / a := by
  -- `b / a` を `r` とおく
  set r := b / a with hr

  -- ここで `b = a * r` というまだ示していない補題に基づいて `h` を書き換える
  rw [show b = a * r from ?lem] at h
  exact? says
    exact (mul_lt_mul_left ha).mp h

  -- 本来証明項が入るべきところに `?lem` をおいたので，
  -- `case lem` でフォーカスできる
  case lem =>
    -- `r` の定義を展開する
    rw [hr]

    -- 分母を払う
    field_simp

    -- `rw_search` でカタをつける
    rw_search says
      rw [Rat.mul_comm]

/-!
  ## ゴールの状態を確認する

  `show P` でゴールが `⊢ P` であることを確認できます
-/

variable (P Q : Prop)

example (hP: P) (hQ: Q) : P ∧ Q := by
  constructor
  · show P
    exact hP
  · show Q
    exact hQ
