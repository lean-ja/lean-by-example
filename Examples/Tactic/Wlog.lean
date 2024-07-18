/- # wlog

`wlog` は、数学でよく使われる、一般性を失うことなく(without loss of generarity)何々と仮定してよいというフレーズの Lean での対応物です。 -/
import Mathlib.Tactic -- 大雑把に import する

-- `n` と `m` は自然数
variable {n m : ℕ}

example (h : n ≠ m) : 0 < |(n - m : ℤ)| := by
  -- 一般性を失うことなく `m < n` と仮定して良い
  wlog hnm : m < n with H

  -- `m < n` の時に成り立つのであれば、そうでないときも成り立つことを示す
  case inr =>
    -- `m < n` ではないので、`n < m` が成り立つ
    have : m = n ∨ n < m := Nat.eq_or_lt_of_not_lt hnm
    replace : n < m := by aesop

    -- `m < n` の時に成り立つという仮定を利用できる
    replace : 0 < |(m - n : ℤ)| := @H m n h.symm this

    rw [abs_sub_comm]
    assumption

  -- `m < n` と仮定してよいことがわかったので、
  -- `m < n` だとして証明する
  apply abs_pos_of_pos
  simp_all
