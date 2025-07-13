
open Lean Grind

variable {M : Type} [AddCommMonoid M] [Zero M]

set_option warn.sorry false in --#

example (l m n : M) : l + m + n + 0 = m + (l + n) := by
  -- `grind`は本来このゴールを閉じることができるべきだと思うが、現状はできない。
  fail_if_success grind
  sorry
